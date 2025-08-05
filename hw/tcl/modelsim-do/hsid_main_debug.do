# Set variables
set top "hsid_main_tb"
set top_opt "${top}_opt"

# Set up visibility into the design for debugging purposes (+acc)
# Set up coverage options (+cover) (collect branch, condition, expression statement, extended toggle, and finite state machine coverage statistics)
vopt +acc +cover=bcesxf $top -o $top_opt

# Add Assertion, Endpoint, and ImmediateAssert to WildcardFilter
set WildcardFilter "Variable Constant Generic Parameter SpecParam Memory Assertion Endpoint CellInternal ImmediateAssert"

# Add ignore files for coverage if it's necessary

vsim -assertdebug -coverage -cvgperinstance +nowarnTFMPC $top_opt -msgmode both
add wave -group "DUT" /$top/dut/*
add wave -group "FSM" /$top/dut/fsm/*
add wave -group "MSE" /$top/dut/mse/*
add wave -group "MSE Comp" /$top/dut/mse_comp/*
add wave -group "FIFO Cap" /$top/dut/fifo_captured/*
add wave -group "FIFO Ref" /$top/dut/fifo_ref/*

view cover
view assertion