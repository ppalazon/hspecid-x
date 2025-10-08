`timescale 1ns / 1ps

/*
 @WAVEDROM_START
 { "signal": [
 { "name": "clk",         "wave": "p.....", "period": 3 },
 { "name": "rst_n_async", "wave": "0...1...........0.", "node": "....a...........e" },
 { "name": "sync_ff[0]",  "wave": "0.....1.........0.", "node": "......b.........f" },
 { "name": "sync_ff[1]",  "wave": "0........1......0.", "node": ".........c......g" },
 { "name": "rst_n_sync",  "wave": "0........1......0.", "node": ".........d......h" }
 ],
 "edge": [
 "a~>b async deassert sampled",
 "b~>c 1st sync stage",
 "c~>d 2nd sync stage (clean reset)",
 "e~>f async assert (both FFs cleared)",
 "f~>g 1st->2nd stage toward 0",
 "g~>h rst_n_sync asserted (stays 0)"
 ]
 }
 @WAVEDROM_END
 */
module hsid_rst_sync (
    input  logic clk,          // Clock input
    input  logic rst_n_async,  // Asynchronous active-low reset input
    output logic rst_n_sync    // Synchronized active-low reset output
  );

  logic [1:0] sync_ff;

  // Two flip-flop synchronizer
  always_ff @(posedge clk or negedge rst_n_async) begin
    if (!rst_n_async) begin
      sync_ff <= 2'b00;       // Both flops reset asynchronously
    end else begin
      sync_ff <= {sync_ff[0], 1'b1}; // Shift towards 1's
    end
  end

  assign rst_n_sync = sync_ff[1];

endmodule