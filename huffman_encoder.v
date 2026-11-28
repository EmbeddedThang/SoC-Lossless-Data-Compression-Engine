`timescale 1ns/1ps
//============================================================================
// huffman_encoder.v - Canonical Dynamic Huffman Encoder (Block-based)
//
// Nguyen ly hoat dong (2-pass Canonical Huffman cho moi block <= 2^ADDR_W byte):
//   1. Nhan 1 block <= 2^ADDR_W byte vao bo nho block (in_last danh dau byte cuoi)
//      dong thoi dem tan suat xuat hien cua tung gia tri byte (0..255).
//   2. Thu thap cac ky tu co tan suat > 0, dung cay Huffman bang Binary Min-Heap.
//   3. Duyet cay (DFS khong de quy) de lay do dai ma (code_len) cho tung ky tu,
//      sau do sinh ma Canonical Huffman (chuan RFC 1951).
//   4. Phat header block + luong bit da nen (MSB-first, dong goi thanh byte):
//        - Byte 0..1 : orig_len[15:0] (little-endian, so byte goc cua block)
//        - Byte 2    : num_syms - 1   (0..255, tuong ung 1..256 ky tu khac nhau)
//        - Tiep theo : num_syms cap (symbol[7:0], code_len[7:0]) theo thu tu tang dan
//        - Tiep theo : bitstream ma hoa Huffman (MSB-first, padding 0 o byte cuoi)
//      out_last = 1 o byte cuoi cung cua block nen.
//
// Giao dien luong byte valid/ready tuong thich he thong SoC Lossless Compression.
//============================================================================
module huffman_encoder #(
    parameter ADDR_W   = 12,        // kich thuoc block buffer = 2^ADDR_W byte (4096)
    parameter MAX_BITS = 24         // do dai ma Huffman toi da (du cho block <= 65536 B)
)(
    input  wire        clk,
    input  wire        rst_n,

    // ---- luong byte vao ----
    input  wire        in_valid,
    output wire        in_ready,
    input  wire [7:0]  in_data,
    input  wire        in_last,

    // ---- luong byte nen ra ----
    output reg         out_valid,
    input  wire        out_ready,
    output reg  [7:0]  out_data,
    output reg         out_last,

    // ---- trang thai / do hieu nang ----
    output wire        busy,
    output reg  [31:0] cycle_cnt
);

    localparam DEPTH  = (1 << ADDR_W);
    localparam POS_W  = ADDR_W + 1;
    localparam CLEN_W = 5;
    localparam CODE_W = 24;
    localparam BUF_W  = 48;

    // ---- ma hoa trang thai FSM ----
    localparam [4:0] S_IDLE        = 5'd0,
                     S_COLLECT     = 5'd1,
                     S_HEAP_INIT   = 5'd2,
                     S_HEAP_LOOP   = 5'd3,
                     S_HEAP_NEXT   = 5'd4,
                     S_SIFT_CMP    = 5'd5,
                     S_BUILD_POP1  = 5'd6,
                     S_BUILD_POP2  = 5'd7,
                     S_DFS         = 5'd8,
                     S_BL_COUNT    = 5'd9,
                     S_NEXT_CODE   = 5'd10,
                     S_ASSIGN_CODE = 5'd11,
                     S_HDR_LEN0    = 5'd12,
                     S_HDR_LEN1    = 5'd13,
                     S_HDR_NSYM    = 5'd14,
                     S_HDR_SYM     = 5'd15,
                     S_HDR_CLEN    = 5'd16,
                     S_ENC_WAIT    = 5'd17,
                     S_ENC_PUSH    = 5'd18,
                     S_ENC_DRAIN   = 5'd19,
                     S_FLUSH       = 5'd20,
                     S_DONE_WAIT   = 5'd21;

    reg [4:0]        state;
    reg [ADDR_W-1:0] wr_ptr;
    reg [POS_W-1:0]  len;
    reg [POS_W-1:0]  pos;
    reg [8:0]        idx;
    reg [8:0]        num_syms;
    reg [7:0]        hdr_idx;

    // ------------------------------------------------------------------
    // Bo nho block (doc dong bo de Quartus suy ra M10K/M9K)
    // ------------------------------------------------------------------
    reg [ADDR_W-1:0] mem_addr;
    reg [7:0]        mem_q;
    reg [7:0]        mem [0:DEPTH-1];

    assign in_ready = (state == S_IDLE);
    assign busy     = (state != S_IDLE);

    wire wr_en = in_valid & in_ready;
    always @(posedge clk) begin
        if (wr_en) mem[wr_ptr] <= in_data;
        mem_q <= mem[mem_addr];
    end

    // ------------------------------------------------------------------
    // Bang tan suat, Min-Heap, Cay Huffman, va Bang ma Canonical
    // ------------------------------------------------------------------
    reg [POS_W-1:0]  freq       [0:255];
    reg [7:0]        active_sym [0:255];

    reg [POS_W-1:0]  heap_w     [0:255];
    reg [8:0]        heap_id    [0:255];
    reg [8:0]        heap_size;
    reg [8:0]        heap_i;
    reg [8:0]        sift_idx;
    reg [4:0]        sift_ret;

    reg [POS_W-1:0]  w1;
    reg [8:0]        id1;
    reg [8:0]        next_node;
    reg [8:0]        tree_left  [0:254];
    reg [8:0]        tree_right [0:254];

    reg [8:0]        dfs_id     [0:256];
    reg [CLEN_W-1:0] dfs_dep    [0:256];
    reg [8:0]        dfs_sp;

    reg [CLEN_W-1:0] code_len   [0:255];
    reg [CODE_W-1:0] canon_code [0:255];
    reg [8:0]        bl_count   [0:MAX_BITS];
    reg [CODE_W-1:0] next_code  [0:MAX_BITS];
    reg [4:0]        bits;
    reg [CODE_W-1:0] canon_tmp;

    // ---- bo dem dong goi bitstream (MSB-aligned) ----
    reg [BUF_W-1:0]  bit_buf;
    reg [5:0]        bit_cnt;

    // ---- logic to hop cho Min-Heap sift-down ----
    wire [9:0] lc_full  = {sift_idx, 1'b0} + 10'd1;
    wire [9:0] rc_full  = {sift_idx, 1'b0} + 10'd2;
    wire       lc_valid = (lc_full < {1'b0, heap_size});
    wire       rc_valid = (rc_full < {1'b0, heap_size});
    wire [7:0] p_idx    = sift_idx[7:0];
    wire [7:0] lc_idx   = lc_full[7:0];
    wire [7:0] rc_idx   = rc_full[7:0];

    wire lc_lt_p = lc_valid && (
        (heap_w[lc_idx] < heap_w[p_idx]) ||
        ((heap_w[lc_idx] == heap_w[p_idx]) && (heap_id[lc_idx] < heap_id[p_idx]))
    );
    wire [7:0] cand_idx = lc_lt_p ? lc_idx : p_idx;

    wire rc_lt_c = rc_valid && (
        (heap_w[rc_idx] < heap_w[cand_idx]) ||
        ((heap_w[rc_idx] == heap_w[cand_idx]) && (heap_id[rc_idx] < heap_id[cand_idx]))
    );
    wire [7:0] best_idx = rc_lt_c ? rc_idx : cand_idx;

    // ---- tin hieu phu cho Canonical, DFS, va Output ----
    wire [15:0] len16        = {{(16-POS_W){1'b0}}, len};
    wire [8:0]  nsym_m1      = num_syms - 9'd1;
    wire        out_can_send = (!out_valid || out_ready);

    wire [CODE_W-1:0] next_c_w = (canon_tmp + {{(CODE_W-9){1'b0}}, bl_count[bits - 5'd1]}) << 1;

    wire [CLEN_W-1:0] sym_clen = code_len[mem_q];
    wire [CODE_W-1:0] sym_code = canon_code[mem_q];
    wire [5:0]        shift_amt = 6'd48 - bit_cnt - {1'b0, sym_clen};

    wire [8:0]        dfs_top_id  = (dfs_sp > 9'd0) ? dfs_id[dfs_sp - 9'd1]  : 9'd0;
    wire [CLEN_W-1:0] dfs_top_dep = (dfs_sp > 9'd0) ? dfs_dep[dfs_sp - 9'd1] : {CLEN_W{1'b0}};

    integer ri;

    // ------------------------------------------------------------------
    // FSM chinh
    // ------------------------------------------------------------------
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state     <= S_IDLE;
            wr_ptr    <= {ADDR_W{1'b0}};
            len       <= {POS_W{1'b0}};
            pos       <= {POS_W{1'b0}};
            idx       <= 9'd0;
            num_syms  <= 9'd0;
            hdr_idx   <= 8'd0;
            mem_addr  <= {ADDR_W{1'b0}};
            heap_size <= 9'd0;
            heap_i    <= 9'd0;
            sift_idx  <= 9'd0;
            sift_ret  <= S_IDLE;
            w1        <= {POS_W{1'b0}};
            id1       <= 9'd0;
            next_node <= 9'd256;
            dfs_sp    <= 9'd0;
            bits      <= 5'd1;
            canon_tmp <= {CODE_W{1'b0}};
            bit_buf   <= {BUF_W{1'b0}};
            bit_cnt   <= 6'd0;
            out_valid <= 1'b0;
            out_data  <= 8'd0;
            out_last  <= 1'b0;
            cycle_cnt <= 32'd0;
            for (ri = 0; ri < 256; ri = ri + 1) begin
                freq[ri]       <= {POS_W{1'b0}};
                code_len[ri]   <= {CLEN_W{1'b0}};
                canon_code[ri] <= {CODE_W{1'b0}};
            end
            for (ri = 0; ri <= MAX_BITS; ri = ri + 1) begin
                bl_count[ri]  <= 9'd0;
                next_code[ri] <= {CODE_W{1'b0}};
            end
        end else begin
            if (state != S_IDLE) cycle_cnt <= cycle_cnt + 1'b1;
            if (out_valid && out_ready) out_valid <= 1'b0;

            case (state)
            //----------------------------------------------------------
            // Pha 1: Nhan du lieu block & dem tan suat
            //----------------------------------------------------------
            S_IDLE: begin
                if (in_valid) begin
                    freq[in_data] <= freq[in_data] + 1'b1;
                    if (in_last || (wr_ptr == DEPTH - 1)) begin
                        len       <= {1'b0, wr_ptr} + 1'b1;
                        wr_ptr    <= {ADDR_W{1'b0}};
                        idx       <= 9'd0;
                        heap_size <= 9'd0;
                        cycle_cnt <= 32'd0;
                        state     <= S_COLLECT;
                    end else begin
                        wr_ptr    <= wr_ptr + 1'b1;
                    end
                end
            end

            //----------------------------------------------------------
            // Pha 2: Thu thap ky tu co freq > 0 vao Min-Heap, xoa bang cu
            //----------------------------------------------------------
            S_COLLECT: begin
                code_len[idx[7:0]] <= {CLEN_W{1'b0}};
                if (idx <= MAX_BITS) bl_count[idx[4:0]] <= 9'd0;

                if (freq[idx[7:0]] != {POS_W{1'b0}}) begin
                    heap_w[heap_size[7:0]]     <= freq[idx[7:0]];
                    heap_id[heap_size[7:0]]    <= idx;
                    active_sym[heap_size[7:0]] <= idx[7:0];
                    heap_size                  <= heap_size + 1'b1;
                    freq[idx[7:0]]             <= {POS_W{1'b0}};
                end

                if (idx == 9'd255) state <= S_HEAP_INIT;
                else               idx   <= idx + 1'b1;
            end

            //----------------------------------------------------------
            // Pha 3: Khoi tao Heapify (xu ly rieng truong hop 1 ky tu)
            //----------------------------------------------------------
            S_HEAP_INIT: begin
                num_syms <= heap_size;
                if (heap_size <= 9'd1) begin
                    code_len[active_sym[0]]   <= 5'd1;
                    canon_code[active_sym[0]] <= {CODE_W{1'b0}};
                    state                     <= S_HDR_LEN0;
                end else begin
                    heap_i <= (heap_size >> 1) - 9'd1;
                    state  <= S_HEAP_LOOP;
                end
            end

            S_HEAP_LOOP: begin
                sift_idx <= heap_i;
                sift_ret <= S_HEAP_NEXT;
                state    <= S_SIFT_CMP;
            end

            S_HEAP_NEXT: begin
                if (heap_i == 9'd0) begin
                    next_node <= 9'd256;
                    state     <= S_BUILD_POP1;
                end else begin
                    heap_i <= heap_i - 1'b1;
                    state  <= S_HEAP_LOOP;
                end
            end

            //----------------------------------------------------------
            // Ham con Sift-Down tren Min-Heap
            //----------------------------------------------------------
            S_SIFT_CMP: begin
                if (best_idx != p_idx) begin
                    heap_w[p_idx]     <= heap_w[best_idx];
                    heap_id[p_idx]    <= heap_id[best_idx];
                    heap_w[best_idx]  <= heap_w[p_idx];
                    heap_id[best_idx] <= heap_id[p_idx];
                    sift_idx          <= {1'b0, best_idx};
                end else begin
                    state <= sift_ret;
                end
            end

            //----------------------------------------------------------
            // Pha 4: Xay dung cay Huffman bang cach gop 2 nut nho nhat
            //----------------------------------------------------------
            S_BUILD_POP1: begin
                w1         <= heap_w[0];
                id1        <= heap_id[0];
                heap_w[0]  <= heap_w[heap_size - 9'd1];
                heap_id[0] <= heap_id[heap_size - 9'd1];
                heap_size  <= heap_size - 1'b1;
                sift_idx   <= 9'd0;
                sift_ret   <= S_BUILD_POP2;
                state      <= S_SIFT_CMP;
            end

            S_BUILD_POP2: begin
                tree_left[next_node - 9'd256]  <= id1;
                tree_right[next_node - 9'd256] <= heap_id[0];
                if (heap_size == 9'd1) begin
                    dfs_id[0]  <= next_node;
                    dfs_dep[0] <= {CLEN_W{1'b0}};
                    dfs_sp     <= 9'd1;
                    state      <= S_DFS;
                end else begin
                    heap_w[0]  <= w1 + heap_w[0];
                    heap_id[0] <= next_node;
                    next_node  <= next_node + 1'b1;
                    sift_idx   <= 9'd0;
                    sift_ret   <= S_BUILD_POP1;
                    state      <= S_SIFT_CMP;
                end
            end

            //----------------------------------------------------------
            // Pha 5: Duyet DFS khong de quy tinh do dai ma cho tung la
            //----------------------------------------------------------
            S_DFS: begin
                if (dfs_sp == 9'd0) begin
                    idx   <= 9'd0;
                    state <= S_BL_COUNT;
                end else if (dfs_top_id < 9'd256) begin
                    code_len[dfs_top_id[7:0]] <= dfs_top_dep;
                    dfs_sp                    <= dfs_sp - 1'b1;
                end else begin
                    dfs_id[dfs_sp - 9'd1]  <= tree_right[dfs_top_id - 9'd256];
                    dfs_dep[dfs_sp - 9'd1] <= dfs_top_dep + 5'd1;
                    dfs_id[dfs_sp]         <= tree_left[dfs_top_id - 9'd256];
                    dfs_dep[dfs_sp]        <= dfs_top_dep + 5'd1;
                    dfs_sp                 <= dfs_sp + 1'b1;
                end
            end

            //----------------------------------------------------------
            // Pha 6: Sinh ma Canonical Huffman (RFC 1951)
            //----------------------------------------------------------
            S_BL_COUNT: begin
                if (code_len[idx[7:0]] != {CLEN_W{1'b0}}) begin
                    bl_count[code_len[idx[7:0]]] <= bl_count[code_len[idx[7:0]]] + 1'b1;
                end
                if (idx == 9'd255) begin
                    bits      <= 5'd1;
                    canon_tmp <= {CODE_W{1'b0}};
                    state     <= S_NEXT_CODE;
                end else begin
                    idx <= idx + 1'b1;
                end
            end

            S_NEXT_CODE: begin
                canon_tmp       <= next_c_w;
                next_code[bits] <= next_c_w;
                if (bits == MAX_BITS[4:0]) begin
                    idx   <= 9'd0;
                    state <= S_ASSIGN_CODE;
                end else begin
                    bits <= bits + 1'b1;
                end
            end

            S_ASSIGN_CODE: begin
                if (code_len[idx[7:0]] != {CLEN_W{1'b0}}) begin
                    canon_code[idx[7:0]]          <= next_code[code_len[idx[7:0]]];
                    next_code[code_len[idx[7:0]]] <= next_code[code_len[idx[7:0]]] + 1'b1;
                end
                if (idx == 9'd255) state <= S_HDR_LEN0;
                else               idx   <= idx + 1'b1;
            end

            //----------------------------------------------------------
            // Pha 7: Phat Header block (orig_len + num_syms + bang do dai)
            //----------------------------------------------------------
            S_HDR_LEN0: if (out_can_send) begin
                out_valid <= 1'b1;
                out_data  <= len16[7:0];
                out_last  <= 1'b0;
                state     <= S_HDR_LEN1;
            end

            S_HDR_LEN1: if (out_can_send) begin
                out_valid <= 1'b1;
                out_data  <= len16[15:8];
                out_last  <= 1'b0;
                state     <= S_HDR_NSYM;
            end

            S_HDR_NSYM: if (out_can_send) begin
                out_valid <= 1'b1;
                out_data  <= nsym_m1[7:0];
                out_last  <= 1'b0;
                hdr_idx   <= 8'd0;
                state     <= S_HDR_SYM;
            end

            S_HDR_SYM: if (out_can_send) begin
                out_valid <= 1'b1;
                out_data  <= active_sym[hdr_idx];
                out_last  <= 1'b0;
                state     <= S_HDR_CLEN;
            end

            S_HDR_CLEN: if (out_can_send) begin
                out_valid <= 1'b1;
                out_data  <= {3'd0, code_len[active_sym[hdr_idx]]};
                out_last  <= 1'b0;
                if ({1'b0, hdr_idx} == nsym_m1) begin
                    pos      <= {POS_W{1'b0}};
                    mem_addr <= {ADDR_W{1'b0}};
                    bit_buf  <= {BUF_W{1'b0}};
                    bit_cnt  <= 6'd0;
                    state    <= S_ENC_WAIT;
                end else begin
                    hdr_idx <= hdr_idx + 1'b1;
                    state   <= S_HDR_SYM;
                end
            end

            //----------------------------------------------------------
            // Pha 8: Ma hoa tung byte va dong goi bit (MSB-first)
            //----------------------------------------------------------
            S_ENC_WAIT: begin
                state <= S_ENC_PUSH;
            end

            S_ENC_PUSH: begin
                bit_buf <= bit_buf | ({24'd0, sym_code} << shift_amt);
                bit_cnt <= bit_cnt + {1'b0, sym_clen};
                pos     <= pos + 1'b1;
                if ((pos + 1'b1) == len) state <= S_FLUSH;
                else                     state <= S_ENC_DRAIN;
            end

            S_ENC_DRAIN: begin
                if (bit_cnt >= 6'd8) begin
                    if (out_can_send) begin
                        out_valid <= 1'b1;
                        out_data  <= bit_buf[47:40];
                        out_last  <= 1'b0;
                        bit_buf   <= bit_buf << 8;
                        bit_cnt   <= bit_cnt - 6'd8;
                    end
                end else begin
                    mem_addr <= pos[ADDR_W-1:0];
                    state    <= S_ENC_WAIT;
                end
            end

            //----------------------------------------------------------
            // Pha 9: Xa not cac bit con lai va phat out_last
            //----------------------------------------------------------
            S_FLUSH: begin
                if (bit_cnt > 6'd8) begin
                    if (out_can_send) begin
                        out_valid <= 1'b1;
                        out_data  <= bit_buf[47:40];
                        out_last  <= 1'b0;
                        bit_buf   <= bit_buf << 8;
                        bit_cnt   <= bit_cnt - 6'd8;
                    end
                end else begin
                    if (out_can_send) begin
                        out_valid <= 1'b1;
                        out_data  <= bit_buf[47:40];
                        out_last  <= 1'b1;
                        bit_buf   <= {BUF_W{1'b0}};
                        bit_cnt   <= 6'd0;
                        state     <= S_DONE_WAIT;
                    end
                end
            end

            S_DONE_WAIT: begin
                if (out_valid && out_ready) begin
                    out_valid <= 1'b0;
                    out_last  <= 1'b0;
                    state     <= S_IDLE;
                end
            end

            default: state <= S_IDLE;
            endcase
        end
    end

endmodule
