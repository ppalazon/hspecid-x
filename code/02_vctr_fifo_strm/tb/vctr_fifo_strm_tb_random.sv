// import vctr_fifo_strm_tb_pkg::*;

class VctrFifoStreamGen;

  rand logic [`DATA_WIDTH-1:0] vctr1 [`VECTOR_LENGTH];
  rand logic [`DATA_WIDTH-1:0] vctr2 [`VECTOR_LENGTH];


  // Generate random vectors
  constraint c_vctrs {
    foreach (vctr1[i]) vctr1[i] inside {[0:(1 << `DATA_WIDTH)-1]};
    foreach (vctr2[i]) vctr2[i] inside {[0:(1 << `DATA_WIDTH)-1]};
  }

  function automatic void sum_vctr(
      output logic [`DATA_WIDTH-1:0]   sum [`VECTOR_LENGTH] // wider to hold overflow
    );
    for (int i = 0; i < `VECTOR_LENGTH; i++) begin
      sum[i] = vctr1[i] + vctr2[i];
    end
  endfunction

endclass