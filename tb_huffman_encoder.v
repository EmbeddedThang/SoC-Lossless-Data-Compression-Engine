`timescale 1ns/1ps
//============================================================================
// tb_huffman_encoder.v - Testbench tu kiem tra (self-checking) cho huffman_encoder
//
// CACH KIEM TRA:
//   1. Day 1 block du lieu vao DUT (co the chen khoang trong ngau nhien tren in_valid).
//   2. Monitor bat luong byte nen ra (co the ep backpressure ngau nhien tren out_ready).
//   3. Giai nen bang mo hinh Canonical Huffman Decoder trong testbench:
//        - Doc header (orig_len, num_syms, bang (sym, code_len))
//        - Tai tao bang ma Canonical Huffman giong het thuat toan chuan
//        - Giai ma bitstream tung bit de khoi phuc dung orig_len byte
//   4. So sanh tung byte giai nen voi du lieu goc => chung minh lossless 100%.
//   5. Kiem tra cac truong hop bien, du lieu lap, van ban, hon hop, ngau nhien,
//      full block, va nhieu block lien tiep.
//
// Chay tren ModelSim/Questa:
//   vlib work
//   vlog huffman_encoder.v tb_huffman_encoder.v
//   vsim -c tb_huffman_encoder -do "run -all; quit"
//============================================================================
module tb_huffman_encoder;

    parameter ADDR_W = 12;
    parameter DEPTH  = (1 << ADDR_W);

    // ---------------- clock / reset ----------------
    reg clk   = 1'b0;
    reg rst_n = 1'b0;
    always #10 clk = ~clk; // 50 MHz

    // ---------------- DUT ----------------
    reg        in_valid = 1'b0;
    wire       in_ready;
    reg  [7:0] in_data  = 8'd0;
    reg        in_last  = 1'b0;

    wire        out_valid;
    reg         out_ready = 1'b0;
    wire [7:0]  out_data;
    wire        out_last;
    wire        busy;
    wire [31:0] cycle_cnt;

    huffman_encoder #(
        .ADDR_W  (ADDR_W),
        .MAX_BITS(24)
    ) dut (
        .clk(clk), .rst_n(rst_n),
        .in_valid(in_valid), .in_ready(in_ready), .in_data(in_data), .in_last(in_last),
        .out_valid(out_valid), .out_ready(out_ready), .out_data(out_data), .out_last(out_last),
        .busy(busy), .cycle_cnt(cycle_cnt)
    );

    // ---------------- du lieu & scoreboard ----------------
    localparam MAX_COMP = DEPTH * 2 + 1024;
    reg [7:0] src  [0:DEPTH-1];
    reg [7:0] comp [0:MAX_COMP-1];
    reg [7:0] dec  [0:DEPTH-1];

    integer   seed   = 32'h2026_0110;
    integer   comp_n;
    integer   dec_n;
    integer   errors = 0;
    integer   tests  = 0;
    reg       blk_done;
    reg       bp_en  = 1'b0;

    // out_ready: luon 1, hoac ngau nhien ~75% san sang khi bp_en = 1
    always @(posedge clk) begin
        if (bp_en) out_ready <= (($random(seed) & 3) != 0);
        else       out_ready <= 1'b1;
    end

    // ---------------- monitor bat luong byte nen ra ----------------
    always @(posedge clk) begin
        if (out_valid && out_ready) begin
            if (comp_n < MAX_COMP) begin
                comp[comp_n] = out_data;
                comp_n = comp_n + 1;
            end else begin
                $display("  [ERR] du lieu nen vuot qua bo dem comp");
                errors = errors + 1;
            end
            if (out_last) blk_done = 1'b1;
        end
    end

    // ---------------- Canonical Huffman Decoder (mo hinh kiem tra) ----------------
    reg [4:0]  d_clen   [0:255];
    reg [23:0] d_code   [0:255];
    reg [8:0]  d_blcnt  [0:24];
    reg [23:0] d_nextc  [0:24];

    task decode_block;
        output integer out_len;
        output integer dec_err;
        integer p, i, b, nsym, orig_len;
        integer bit_pos, total_bits, matched, cur_len;
        reg [23:0] cur_code;
        reg [7:0]  sym;
        reg [4:0]  cl;
        begin
            dec_err = 0;
            out_len = 0;
            if (comp_n < 5) begin
                $display("  [ERR] header qua ngan (%0d B)", comp_n);
                dec_err = 1;
            end else begin
                orig_len = comp[0] + (comp[1] << 8);
                nsym     = comp[2] + 1;
                p        = 3;

                if (comp_n < p + 2 * nsym) begin
                    $display("  [ERR] thieu bang ky tu trong header");
                    dec_err = 1;
                end else begin
                    for (i = 0; i < 256; i = i + 1) begin
                        d_clen[i] = 5'd0;
                        d_code[i] = 24'd0;
                    end
                    for (i = 0; i <= 24; i = i + 1) begin
                        d_blcnt[i] = 9'd0;
                        d_nextc[i] = 24'd0;
                    end

                    for (i = 0; i < nsym; i = i + 1) begin
                        sym = comp[p];
                        cl  = comp[p + 1][4:0];
                        p   = p + 2;
                        d_clen[sym] = cl;
                        if (cl == 0 || cl > 24) begin
                            $display("  [ERR] code_len khong hop le: %0d", cl);
                            dec_err = 1;
                        end else begin
                            d_blcnt[cl] = d_blcnt[cl] + 1;
                        end
                    end

                    // Tai tao ma Canonical
                    d_nextc[0] = 24'd0;
                    cur_code   = 24'd0;
                    for (b = 1; b <= 24; b = b + 1) begin
                        cur_code   = (cur_code + d_blcnt[b - 1]) << 1;
                        d_nextc[b] = cur_code;
                    end
                    for (i = 0; i < 256; i = i + 1) begin
                        if (d_clen[i] != 0) begin
                            d_code[i] = d_nextc[d_clen[i]];
                            d_nextc[d_clen[i]] = d_nextc[d_clen[i]] + 1;
                        end
                    end

                    // Giai ma bitstream MSB-first
                    bit_pos    = 0;
                    total_bits = (comp_n - p) * 8;
                    while (out_len < orig_len && !dec_err) begin
                        cur_code = 24'd0;
                        cur_len  = 0;
                        matched  = 0;
                        while (!matched && cur_len < 24 && !dec_err) begin
                            if (bit_pos >= total_bits) begin
                                $display("  [ERR] het bit khi moi giai nen %0d/%0d B", out_len, orig_len);
                                dec_err = 1;
                            end else begin
                                cur_code = (cur_code << 1) | ((comp[p + (bit_pos >> 3)] >> (7 - (bit_pos & 7))) & 1'b1);
                                cur_len  = cur_len + 1;
                                bit_pos  = bit_pos + 1;
                                for (i = 0; i < 256; i = i + 1) begin
                                    if (!matched && d_clen[i] == cur_len && d_code[i] == cur_code) begin
                                        dec[out_len] = i[7:0];
                                        out_len = out_len + 1;
                                        matched = 1;
                                    end
                                end
                            end
                        end
                        if (!matched && !dec_err) begin
                            $display("  [ERR] khong khop duoc ma Huffman tai byte %0d", out_len);
                            dec_err = 1;
                        end
                    end
                end
            end
        end
    endtask

    // ---------------- cac task sinh du lieu ----------------
    integer g;

    task gen_const;
        input integer n;
        input [7:0]   v;
        begin for (g = 0; g < n; g = g + 1) src[g] = v; end
    endtask

    task gen_random;
        input integer n;
        begin for (g = 0; g < n; g = g + 1) src[g] = $random(seed); end
    endtask

    task gen_skewed;
        input integer n;
        integer r;
        begin
            for (g = 0; g < n; g = g + 1) begin
                r = ($random(seed) & 32'h7fff_ffff) % 100;
                if      (r < 50) src[g] = 8'h41; // 'A' 50%
                else if (r < 75) src[g] = 8'h42; // 'B' 25%
                else if (r < 90) src[g] = 8'h43; // 'C' 15%
                else             src[g] = 8'h44 + (r & 3);
            end
        end
    endtask

    task gen_text;
        input integer n;
        reg [8*44-1:0] s;
        integer idx;
        begin
            s = "the quick brown fox jumps over the lazy dog ";
            for (g = 0; g < n; g = g + 1) begin
                idx = g % 44;
                src[g] = s[8*(43-idx) +: 8];
                if (($random(seed) & 63) == 0) src[g] = "A" + ($random(seed) & 15);
            end
        end
    endtask

    task gen_all_syms;
        input integer n;
        begin
            for (g = 0; g < n; g = g + 1) begin
                if (g < 256) src[g] = g[7:0];
                else         src[g] = ($random(seed) & 7); // lech tan suat sau 256 byte dau
            end
        end
    endtask

    // ---------------- task chay 1 block ----------------
    task run_block;
        input integer    n;
        input integer    gap;       // 1: chen khoang trong ngau nhien tren in_valid
        input integer    bp;        // 1: backpressure ngau nhien tren out_ready
        input integer    max_ratio; // gioi han % kich thuoc nen toi da (0 = khong ep)
        input [8*24-1:0] name;
        integer k, tmo, bad, dec_err, ratio;
        begin
            tests = tests + 1;
            comp_n = 0; dec_n = 0; blk_done = 1'b0;
            bp_en = (bp != 0);

            for (k = 0; k < n; k = k + 1) begin
                if (gap != 0 && (($random(seed) & 3) == 0)) begin
                    in_valid <= 1'b0;
                    @(posedge clk);
                end
                in_valid <= 1'b1;
                in_data  <= src[k];
                in_last  <= (k == n - 1);
                @(posedge clk);
                while (!in_ready) @(posedge clk);
            end
            in_valid <= 1'b0;
            in_last  <= 1'b0;

            tmo = 0;
            while (!blk_done && tmo < 500_000) begin
                @(posedge clk);
                tmo = tmo + 1;
            end
            @(posedge clk);
            @(posedge clk);

            bad = 0;
            if (!blk_done) begin
                $display("  [ERR] TIMEOUT (khong thay out_last)");
                bad = 1;
            end else begin
                decode_block(dec_n, dec_err);
                if (dec_err) begin
                    bad = 1;
                end else if (dec_n != n) begin
                    $display("  [ERR] sai so byte: goc=%0d, giai nen=%0d", n, dec_n);
                    bad = 1;
                end else begin
                    for (k = 0; k < n && !bad; k = k + 1)
                        if (dec[k] !== src[k]) begin
                            $display("  [ERR] byte %0d khac: goc=%02h, giai nen=%02h", k, src[k], dec[k]);
                            bad = 1;
                        end
                end
            end

            if (busy) begin
                $display("  [ERR] DUT van busy sau out_last");
                bad = 1;
            end

            ratio = (n > 0) ? ((comp_n * 100) / n) : 0;
            if (max_ratio > 0 && ratio > max_ratio) begin
                $display("  [ERR] ti le nen kem: %0d%% > muc cho phep %0d%%", ratio, max_ratio);
                bad = 1;
            end

            if (bad) errors = errors + 1;

            $display("[%s] in=%5d B -> out=%5d B (%3d%%)  %6d cyc (%0d.%02d cyc/B)  %s",
                     name, n, comp_n, ratio,
                     cycle_cnt, cycle_cnt / n, ((cycle_cnt * 100) / n) % 100,
                     bad ? "FAIL" : "PASS");
        end
    endtask

    // ---------------- kich ban test ----------------
    integer t, sz;
    initial begin
        repeat (5) @(posedge clk);
        rst_n <= 1'b1;
        repeat (3) @(posedge clk);

        $display("==== Huffman encoder testbench ====");

        // 1. Bien gioi: 1 byte, 2 byte, 3 byte giong nhau
        src[0] = 8'h41;                                 run_block(1, 0, 0, 0,  "1 byte");
        src[0] = 8'h41; src[1] = 8'h42;                 run_block(2, 0, 0, 0,  "2 byte khac nhau");
        src[0] = 8'h61; src[1] = 8'h61; src[2] = 8'h61; run_block(3, 0, 0, 0,  "3 byte giong nhau");

        // 2. Du lieu hang (1 ky tu duy nhat)
        gen_const(100,  8'h00);                         run_block(100,  0, 0, 25, "100 x 0x00");
        gen_const(1000, 8'hFF);                         run_block(1000, 0, 0, 20, "1000 x 0xFF");

        // 3. Tan suat lech (Huffman nen rat tot)
        gen_skewed(1000);                               run_block(1000, 0, 0, 35, "skewed 1000B");
        gen_skewed(2000);                               run_block(2000, 1, 1, 35, "skewed + gap + bp");

        // 4. Van ban tieng Anh lap lai
        gen_text(2000);                                 run_block(2000, 0, 0, 65, "van ban 2000B");
        gen_text(2000);                                 run_block(2000, 1, 1, 65, "van ban + gap + bp");

        // 5. Du 256 gia tri byte khac nhau
        gen_all_syms(1024);                             run_block(1024, 0, 0, 0,  "all 256 symbols");

        // 6. Ngau nhien thuan tuy (kiem tra lossless khi kho nen)
        gen_random(1000);                               run_block(1000, 0, 0, 0,  "random 1000B");

        // 7. Block day (DEPTH = 4096 B)
        gen_text(DEPTH);                                run_block(DEPTH, 0, 0, 60, "text full 4096B");
        gen_const(DEPTH, 8'h5A);                        run_block(DEPTH, 1, 1, 18, "const full + gap + bp");

        // 8. Nhieu block lien tiep voi kich thuoc ngau nhien (kiem tra reset trang thai)
        for (t = 0; t < 15; t = t + 1) begin
            sz = 1 + (($random(seed) & 32'h7fff_ffff) % DEPTH);
            case (t % 3)
                0: gen_skewed(sz);
                1: gen_text(sz);
                2: gen_random(sz);
            endcase
            run_block(sz, t & 1, (t >> 1) & 1, 0, "block ngau nhien");
        end

        $display("==================================");
        if (errors == 0) $display("KET QUA: ALL %0d TESTS PASSED", tests);
        else             $display("KET QUA: FAILED - %0d loi / %0d test", errors, tests);
        $finish;
    end

    // watchdog toan cuc
    initial begin
        #500_000_000;
        $display("WATCHDOG: mo phong chay qua lau");
        $finish;
    end

endmodule
