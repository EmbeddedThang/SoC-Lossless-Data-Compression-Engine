
//   1. Nhan 1 block <= 2^ADDR_W byte vao bo nho (in_last danh dau byte cuoi).
//   2. Sau do quet block: tai moi vi tri `pos`
//        - lay 3 byte tai pos, bam ra HASH_W bit
//        - tra bang head[hash] -> vi tri gan nhat co cung hash (ung vien)
//        - so sanh that su tung byte -> do dai khop (mlen)
//        - mlen >= 3  -> phat token MATCH(length, distance)
//          nguoc lai -> phat token LITERAL(byte)
//   3. Do buoc so sanh byte-by-byte nen va cham hash KHONG gay sai ket qua,
//      chi lam giam ti le nen. Do do KHONG can xoa bang head giua cac block.
//
// GIAO DIEN TOKEN (de khoi Huffman / DEFLATE phia sau noi vao)
//   tok_valid/tok_ready : handshake kieu valid/ready
//   tok_is_match = 0 : LITERAL, du lieu o tok_literal
//   tok_is_match = 1 : MATCH,   do dai tok_length (3..MAX_LEN),
//                               khoang cach tok_distance (1..MAX_DIST)
//   tok_last = 1 : token cuoi cung cua block
//   Khoang cach tinh nguoc tu vi tri hien tai; distance < length la hop le
//   (overlap), phia giai nen phai copy tung byte.
//
// GIOI HAN
//   - Lich su (window) chi la phan du lieu da co trong block hien tai
//     (khong giu lich su qua block). Block lon -> window lon -> ti le nen tot.
//   - Neu du 2^ADDR_W byte ma chua co in_last, block tu dong ket thuc.
//   - MAX_LEN <= 511 (tok_length 9 bit), MAX_DIST <= 2^ADDR_W - 1.
//============================================================================
module lz77_encoder #(
    parameter ADDR_W   = 12,        // block buffer = 2^ADDR_W byte (4096)
    parameter HASH_W   = 12,        // so bit hash (bang head 2^HASH_W muc)
    parameter MAX_LEN  = 258,       // do dai match toi da (chuan DEFLATE)
    parameter MAX_DIST = 4095       // khoang cach toi da (<= 2^ADDR_W - 1)
)(
    input  wire              clk,
    input  wire              rst_n,

    // ---- luong byte vao ----
    input  wire              in_valid,
    output wire              in_ready,
    input  wire [7:0]        in_data,
    input  wire              in_last,        // byte cuoi cua block

    // ---- luong token ra ----
    output reg               tok_valid,
    input  wire              tok_ready,
    output reg               tok_is_match,
    output reg  [7:0]        tok_literal,
    output reg  [8:0]        tok_length,
    output reg  [ADDR_W-1:0] tok_distance,
    output reg               tok_last,

    // ---- trang thai / do hieu nang ----
    output wire              busy,
    output reg  [31:0]       cycle_cnt       // so chu ky de nen block gan nhat
);

    localparam DEPTH     = (1 << ADDR_W);
    localparam POS_W     = ADDR_W + 1;       // du de bieu dien len = DEPTH
    localparam MIN_MATCH = 3;

    // ---- ma hoa trang thai ----
    localparam [3:0] S_IDLE   = 4'd0,   // nhan du lieu vao
                     S_FETCH  = 4'd1,   // doc 3 byte tai pos
                     S_HASH   = 4'd2,   // tinh hash
                     S_HWAIT  = 4'd3,   // cho RAM bang head
                     S_HGOT   = 4'd4,   // lay ung vien, cap nhat head
                     S_CISSUE = 4'd5,   // phat dia chi so sanh
                     S_CWAIT  = 4'd6,   // cho RAM
                     S_CCHK   = 4'd7,   // so sanh 1 byte
                     S_DECIDE = 4'd8,   // chon literal / match
                     S_EMIT   = 4'd9;   // dua token ra, cho tok_ready

    reg [3:0]        state;
    reg [ADDR_W-1:0] wr_ptr;            // con tro ghi khi nhan du lieu
    reg [POS_W-1:0]  len;               // so byte cua block
    reg [POS_W-1:0]  pos;               // vi tri dang xu ly
    reg [POS_W-1:0]  step;              // so byte token hien tai bao phu
    reg [2:0]        fc;                // dem pha FETCH
    reg [7:0]        b0, b1, b2;        // 3 byte tai pos
    reg [ADDR_W-1:0] cand;              // vi tri ung vien
    reg [8:0]        mlen;              // do dai khop hien tai

    wire [31:0]      mlen32  = {23'd0, mlen};          // mo rong an toan (khong phu thuoc ADDR_W)
    wire [ADDR_W-1:0] mlen_a = mlen32[ADDR_W-1:0];

    wire [POS_W-1:0] rem     = len - pos;
    wire [POS_W-1:0] max_cmp = (rem > MAX_LEN) ? MAX_LEN : rem;

    // ------------------------------------------------------------------
    // Bo nho block (2 ban sao de co 2 cong doc doc lap: pos+k va cand+k).
    // Doc dong bo (q <= mem[addr]) de Quartus suy ra M10K/M9K.
    // Dia chi dat o chu ky C -> du lieu hop le o chu ky C+2
    // (dia chi la thanh ghi, RAM chot du lieu o canh ke tiep).
    // ------------------------------------------------------------------
    reg [ADDR_W-1:0] a_addr, b_addr;
    reg [7:0]        a_q,    b_q;
    reg [7:0]        mem_a [0:DEPTH-1];
    reg [7:0]        mem_b [0:DEPTH-1];

    assign in_ready = (state == S_IDLE);
    wire   wr_en    = in_valid & in_ready;

    always @(posedge clk) begin
        if (wr_en) mem_a[wr_ptr] <= in_data;
        a_q <= mem_a[a_addr];
    end

    always @(posedge clk) begin
        if (wr_en) mem_b[wr_ptr] <= in_data;
        b_q <= mem_b[b_addr];
    end

    // ------------------------------------------------------------------
    // Bang hash head[hash] = vi tri gan nhat co hash do.
    // Khoi tao 0 de mo phong khong bi X; khong can xoa giua cac block
    // vi ung vien luon duoc kiem chung bang so sanh that su.
    // ------------------------------------------------------------------
    reg [HASH_W-1:0] h_addr;
    reg [ADDR_W-1:0] h_q;
    reg [ADDR_W-1:0] head [0:(1<<HASH_W)-1];
    integer hi;
    initial for (hi = 0; hi < (1<<HASH_W); hi = hi + 1) head[hi] = {ADDR_W{1'b0}};

    wire head_we = (state == S_HGOT);
    always @(posedge clk) begin
        if (head_we) head[h_addr] <= pos[ADDR_W-1:0];
        h_q <= head[h_addr];
    end

    // ---- ham bam 3 byte -> HASH_W bit (gap XOR) ----
    wire [23:0]        hx   = {b0, b1, b2};
    wire [23:0]        hf   = hx ^ (hx >> HASH_W);
    wire [HASH_W-1:0]  hash = hf[HASH_W-1:0];

    // ---- kiem tra ung vien hop le ----
    wire [ADDR_W-1:0] pos_a   = pos[ADDR_W-1:0];
    wire              cand_ok = (h_q < pos_a) && ((pos_a - h_q) <= MAX_DIST);

    // ---- buoc cua token chuan bi phat ----
    wire [POS_W-1:0]  step_w  = (mlen >= MIN_MATCH) ? mlen32[POS_W-1:0]
                                                    : {{(POS_W-1){1'b0}}, 1'b1};

    assign busy = (state != S_IDLE);

    // ------------------------------------------------------------------
    // FSM chinh
    // ------------------------------------------------------------------
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state        <= S_IDLE;
            wr_ptr       <= {ADDR_W{1'b0}};
            len          <= {POS_W{1'b0}};
            pos          <= {POS_W{1'b0}};
            step         <= {POS_W{1'b0}};
            fc           <= 3'd0;
            mlen         <= 9'd0;
            cand         <= {ADDR_W{1'b0}};
            a_addr       <= {ADDR_W{1'b0}};
            b_addr       <= {ADDR_W{1'b0}};
            h_addr       <= {HASH_W{1'b0}};
            tok_valid    <= 1'b0;
            tok_is_match <= 1'b0;
            tok_literal  <= 8'd0;
            tok_length   <= 9'd0;
            tok_distance <= {ADDR_W{1'b0}};
            tok_last     <= 1'b0;
            cycle_cnt    <= 32'd0;
        end else begin
            if (state != S_IDLE) cycle_cnt <= cycle_cnt + 1'b1;

            case (state)
            //----------------------------------------------------------
            S_IDLE: begin
                if (in_valid) begin
                    if (in_last || (wr_ptr == DEPTH-1)) begin
                        len       <= {1'b0, wr_ptr} + 1'b1;
                        wr_ptr    <= {ADDR_W{1'b0}};
                        pos       <= {POS_W{1'b0}};
                        fc        <= 3'd0;
                        cycle_cnt <= 32'd0;
                        state     <= S_FETCH;
                    end else begin
                        wr_ptr    <= wr_ptr + 1'b1;
                    end
                end
            end
            //----------------------------------------------------------
            // Doc 3 byte pos, pos+1, pos+2 (pipeline, do tre RAM = 2)
            S_FETCH: begin
                case (fc)
                    3'd0: begin a_addr <= pos_a;          fc <= 3'd1; end
                    3'd1: begin a_addr <= pos_a + 1'b1;   fc <= 3'd2; end
                    3'd2: begin a_addr <= pos_a + 2'd2;
                                b0     <= a_q;            fc <= 3'd3; end
                    3'd3: begin b1     <= a_q;            fc <= 3'd4; end
                    3'd4: begin b2     <= a_q;            fc <= 3'd0;
                                state  <= S_HASH; end
                    default: fc <= 3'd0;
                endcase
            end
            //----------------------------------------------------------
            S_HASH: begin
                mlen <= 9'd0;
                if (rem < MIN_MATCH) begin
                    state  <= S_DECIDE;          // con < 3 byte: chi co the literal
                end else begin
                    h_addr <= hash;
                    state  <= S_HWAIT;
                end
            end
            //----------------------------------------------------------
            S_HWAIT: state <= S_HGOT;
            //----------------------------------------------------------
            S_HGOT: begin                         // head[h_addr] <= pos (head_we)
                cand <= h_q;
                if (cand_ok) state <= S_CISSUE;
                else         state <= S_DECIDE;   // khong co ung vien -> literal
            end
            //----------------------------------------------------------
            S_CISSUE: begin
                a_addr <= pos_a + mlen_a;
                b_addr <= cand  + mlen_a;
                state  <= S_CWAIT;
            end
            S_CWAIT: state <= S_CCHK;
            //----------------------------------------------------------
            S_CCHK: begin
                if (a_q == b_q) begin
                    mlen <= mlen + 1'b1;
                    if ((mlen + 1) < max_cmp) state <= S_CISSUE;
                    else                      state <= S_DECIDE;
                end else begin
                    state <= S_DECIDE;
                end
            end
            //----------------------------------------------------------
            S_DECIDE: begin
                if (mlen >= MIN_MATCH) begin
                    tok_is_match <= 1'b1;
                    tok_literal  <= 8'd0;
                    tok_length   <= mlen;
                    tok_distance <= pos_a - cand;
                end else begin
                    tok_is_match <= 1'b0;
                    tok_literal  <= b0;
                    tok_length   <= 9'd0;
                    tok_distance <= {ADDR_W{1'b0}};
                end
                step      <= step_w;
                tok_last  <= ((pos + step_w) >= len);
                tok_valid <= 1'b1;
                state     <= S_EMIT;
            end
            //----------------------------------------------------------
            S_EMIT: begin
                if (tok_ready) begin
                    tok_valid <= 1'b0;
                    if (tok_last) begin
                        state <= S_IDLE;
                    end else begin
                        pos   <= pos + step;
                        fc    <= 3'd0;
                        state <= S_FETCH;
                    end
                end
            end
            //----------------------------------------------------------
            default: state <= S_IDLE;
            endcase
        end
    end

endmodule