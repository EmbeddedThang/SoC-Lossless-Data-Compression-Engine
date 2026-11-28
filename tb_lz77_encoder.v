`timescale 1ns/1ps
//============================================================================
// tb_lz77_encoder.v  -  Testbench tu kiem tra (self-checking) cho lz77_encoder
//
// CACH KIEM TRA
//   1. Day 1 block du lieu vao DUT (co the chen khoang trong ngau nhien).
//   2. Monitor bat moi token ra (co the ep backpressure ngau nhien) va
//      GIAI NEN ngay trong testbench (mo hinh decoder bang hanh vi).
//   3. Cuoi block so sanh du lieu giai nen voi du lieu goc  => chung minh lossless.
//   4. Kiem tra them: length trong [3, MAX_LEN], distance trong [1, MAX_DIST]
//      va khong tro ra truoc dau block.
//
// CHAY (Icarus Verilog):
//   iverilog -g2005 -o sim lz77_encoder.v tb_lz77_encoder.v && vvp sim
// ModelSim/Questa: vlog lz77_encoder.v tb_lz77_encoder.v; vsim -c tb_lz77_encoder -do "run -all"
//============================================================================
module tb_lz77_encoder;

    parameter ADDR_W   = 12;
    parameter DEPTH    = (1 << ADDR_W);
    parameter MAX_LEN  = 258;
    parameter MAX_DIST = DEPTH - 1;

    // ---------------- clock / reset ----------------
    reg clk   = 1'b0;
    reg rst_n = 1'b0;
    always #10 clk = ~clk;                       // 50 MHz

    // ---------------- DUT ----------------
    reg                in_valid = 1'b0;
    wire               in_ready;
    reg  [7:0]         in_data  = 8'd0;
    reg                in_last  = 1'b0;

    wire               tok_valid;
    reg                tok_ready = 1'b0;
    wire               tok_is_match;
    wire [7:0]         tok_literal;
    wire [8:0]         tok_length;
    wire [ADDR_W-1:0]  tok_distance;
    wire               tok_last;
    wire               busy;
    wire [31:0]        cycle_cnt;

    lz77_encoder #(
        .ADDR_W  (ADDR_W),
        .HASH_W  (12),
        .MAX_LEN (MAX_LEN),
        .MAX_DIST(MAX_DIST)
    ) dut (
        .clk(clk), .rst_n(rst_n),
        .in_valid(in_valid), .in_ready(in_ready), .in_data(in_data), .in_last(in_last),
        .tok_valid(tok_valid), .tok_ready(tok_ready),
        .tok_is_match(tok_is_match), .tok_literal(tok_literal),
        .tok_length(tok_length), .tok_distance(tok_distance), .tok_last(tok_last),
        .busy(busy), .cycle_cnt(cycle_cnt)
    );

    // ---------------- du lieu & scoreboard ----------------
    reg [7:0] src [0:DEPTH-1];                   // du lieu goc
    reg [7:0] dec [0:DEPTH-1];                   // du lieu giai nen lai tu token
    integer   seed = 32'h1234_5678;
    integer   dec_n;
    integer   n_lit, n_match, match_bytes;
    integer   errors = 0;
    integer   tests  = 0;
    reg       blk_done;
    reg       bp_en = 1'b0;                      // 1: backpressure ngau nhien tren tok_ready

    // tok_ready: luon 1, hoac ngau nhien khi bp_en
    always @(posedge clk) begin
        if (bp_en) tok_ready <= (($random(seed) & 3) != 0);   // ~75% san sang
        else       tok_ready <= 1'b1;
    end

    // ---------------- monitor + decoder mo hinh ----------------
    integer j;
    always @(posedge clk) begin
        if (tok_valid && tok_ready) begin
            if (tok_is_match) begin
                if (tok_length < 3 || tok_length > MAX_LEN) begin
                    $display("  [ERR] length ngoai khoang: %0d", tok_length);
                    errors = errors + 1;
                end
                if (tok_distance < 1 || tok_distance > MAX_DIST || tok_distance > dec_n) begin
                    $display("  [ERR] distance sai: %0d (da giai nen %0d byte)", tok_distance, dec_n);
                    errors = errors + 1;
                end else if (dec_n + tok_length > DEPTH) begin
                    $display("  [ERR] match vuot qua kich thuoc block");
                    errors = errors + 1;
                end else begin
                    for (j = 0; j < tok_length; j = j + 1) begin   // copy tung byte (cho phep overlap)
                        dec[dec_n] = dec[dec_n - tok_distance];
                        dec_n = dec_n + 1;
                    end
                end
                n_match     = n_match + 1;
                match_bytes = match_bytes + tok_length;
            end else begin
                if (dec_n < DEPTH) begin
                    dec[dec_n] = tok_literal;
                    dec_n = dec_n + 1;
                end else begin
                    $display("  [ERR] qua nhieu literal");
                    errors = errors + 1;
                end
                n_lit = n_lit + 1;
            end
            if (tok_last) blk_done = 1'b1;
        end
    end

    // ---------------- cac task sinh du lieu ----------------
    integer g;

    task gen_const;                               // toan 1 gia tri
        input integer n;
        input [7:0]   v;
        begin for (g = 0; g < n; g = g + 1) src[g] = v; end
    endtask

    task gen_random;                              // byte ngau nhien (kho nen)
        input integer n;
        begin for (g = 0; g < n; g = g + 1) src[g] = $random(seed); end
    endtask

    task gen_period;                              // lap lai chu ky p byte ngau nhien
        input integer n;
        input integer p;
        begin
            for (g = 0; g < p && g < n; g = g + 1) src[g] = $random(seed);
            for (g = p; g < n; g = g + 1) src[g] = src[g - p];
        end
    endtask

    task gen_text;                                // van ban lap, chen chut thay doi
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

    integer mp, ml, md, mk;
    task gen_mixed;                               // literal xen ke copy doan cu (nhieu khoang cach)
        input integer n;
        begin
            mp = 0;
            while (mp < n) begin
                if (mp < 8 || ($random(seed) & 3) == 0) begin
                    src[mp] = $random(seed);
                    mp = mp + 1;
                end else begin
                    ml = 3 + (($random(seed) & 32'h7fff_ffff) % 60);
                    md = 1 + (($random(seed) & 32'h7fff_ffff) % mp);
                    for (mk = 0; mk < ml && mp < n; mk = mk + 1) begin
                        src[mp] = src[mp - md];
                        mp = mp + 1;
                    end
                end
            end
        end
    endtask

    // ---------------- task chay 1 block ----------------
    task run_block;
        input integer       n;
        input integer       gap;                  // 1: chen khoang trong ngau nhien o dau vao
        input integer       bp;                   // 1: backpressure ngau nhien o dau ra
        input integer       min_mb;               // so byte toi thieu PHAI duoc phu boi match (chong pass "rong")
        input [8*22-1:0]    name;
        integer k, tmo, bad, est_bytes;
        begin
            tests = tests + 1;
            dec_n = 0; blk_done = 1'b0;
            n_lit = 0; n_match = 0; match_bytes = 0;
            bp_en = (bp != 0);

            // ---- gui du lieu ----
            for (k = 0; k < n; k = k + 1) begin
                if (gap != 0 && (($random(seed) & 3) == 0)) begin
                    in_valid <= 1'b0;
                    @(posedge clk);
                end
                in_valid <= 1'b1;
                in_data  <= src[k];
                in_last  <= (k == n - 1);
                @(posedge clk);
                while (!in_ready) @(posedge clk);   // handshake xay ra o canh nay
            end
            in_valid <= 1'b0;
            in_last  <= 1'b0;

            // ---- cho token cuoi ----
            tmo = 0;
            while (!blk_done && tmo < 5_000_000) begin
                @(posedge clk);
                tmo = tmo + 1;
            end
            @(posedge clk);
            @(posedge clk);

            // ---- kiem tra ----
            bad = 0;
            if (!blk_done) begin
                $display("  [ERR] TIMEOUT (khong thay tok_last)");
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
            if (busy) begin
                $display("  [ERR] DUT van busy sau tok_last");
                bad = 1;
            end
            if (match_bytes < min_mb) begin
                $display("  [ERR] nen kem: match chi phu %0d B, yeu cau >= %0d B", match_bytes, min_mb);
                bad = 1;
            end
            if (bad) errors = errors + 1;

            // uoc luong kich thuoc kieu LZSS: literal 9 bit, match 22 bit (1 + 9 + 12)
            est_bytes = (n_lit * 9 + n_match * 22 + 7) / 8;
            $display("[%s] n=%5d  lit=%5d match=%4d (phu %5d B)  ~%5d B (%0d%%)  %7d cyc (%0d.%02d cyc/B)  %s",
                     name, n, n_lit, n_match, match_bytes, est_bytes,
                     (n > 0) ? (est_bytes * 100 / n) : 0,
                     cycle_cnt, cycle_cnt / n, ((cycle_cnt * 100) / n) % 100,
                     bad ? "FAIL" : "PASS");
        end
    endtask

    // ---------------- kich ban test ----------------
    integer t, sz;
    initial begin
        $dumpfile("tb_lz77_encoder.vcd");
        $dumpvars(0, tb_lz77_encoder);

        repeat (5) @(posedge clk);
        rst_n <= 1'b1;
        repeat (3) @(posedge clk);

        $display("==== LZ77 encoder testbench ====");

        // 1. chuoi ngan co lap
        for (t = 0; t < 15; t = t + 1) src[t] = "a" + (t % 3);      // abcabcabc...
        run_block(15,   0, 0, 12,   "abcabc x5");

        // 2. biet gioi: 1, 2, 3 byte
        src[0] = 8'h41;                                    run_block(1, 0, 0, 0, "1 byte");
        src[0] = 8'h41; src[1] = 8'h42;                    run_block(2, 0, 0, 0, "2 byte");
        src[0] = 8'h61; src[1] = 8'h61; src[2] = 8'h61;    run_block(3, 0, 0, 0, "aaa (3 byte)");

        // 3. overlap: distance = 1, length bi chan o MAX_LEN
        gen_const(100,  8'h00);                            run_block(100,  0, 0, 99,   "100 x 0x00");
        gen_const(1000, 8'hFF);                            run_block(1000, 0, 0, 990,  "1000 x 0xFF (cap 258)");

        // 4. chu ky ngan / dai
        gen_period(500, 2);                                run_block(500,  0, 0, 490,  "chu ky 2");
        gen_period(2000, 37);                              run_block(2000, 0, 0, 1900, "chu ky 37");

        // 5. van ban lap
        gen_text(2000);                                    run_block(2000, 0, 0, 1500, "van ban 2000B");
        gen_text(2000);                                    run_block(2000, 1, 1, 1500, "van ban + gap + bp");

        // 6. ngau nhien thuan tuy (khong nen duoc)
        gen_random(1000);                                  run_block(1000, 0, 0, 0,    "random 1000B");

        // 7. hon hop literal/match nhieu khoang cach
        gen_mixed(3000);                                   run_block(3000, 0, 0, 2000, "mixed 3000B");
        gen_mixed(3000);                                   run_block(3000, 1, 1, 2000, "mixed + gap + bp");

        // 8. block day (DEPTH byte)
        gen_mixed(DEPTH);                                  run_block(DEPTH, 0, 0, 3000, "mixed full block");
        gen_const(DEPTH, 8'h5A);                           run_block(DEPTH, 1, 1, 4000, "const full + gap + bp");

        // 9. nhieu block lien tiep, kich thuoc ngau nhien (kiem tra reset trang thai)
        for (t = 0; t < 20; t = t + 1) begin
            sz = 1 + (($random(seed) & 32'h7fff_ffff) % DEPTH);
            case (t % 3)
                0: gen_mixed(sz);
                1: gen_text(sz);
                2: gen_random(sz);
            endcase
            run_block(sz, t & 1, (t >> 1) & 1,
                      ((t % 3 != 2) && (sz >= 500)) ? sz / 2 : 0, "block ngau nhien");
        end

        $display("==================================");
        if (errors == 0) $display("KET QUA: ALL %0d TESTS PASSED", tests);
        else             $display("KET QUA: FAILED - %0d loi / %0d test", errors, tests);
        $finish;
    end

    // watchdog toan cuc
    initial begin
        #2_000_000_000;
        $display("WATCHDOG: mo phong chay qua lau");
        $finish;
    end

endmodule