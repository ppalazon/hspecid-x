# Set variables
set top "hsid_x_top_tb"
set top_opt "${top}_opt"

# Set up visibility into the design for debugging purposes (+acc)
# Set up coverage options (+cover) (collect branch, condition, expression statement, extended toggle, and finite state machine coverage statistics)
vopt +acc +cover=bcesxf $top -o $top_opt

# Add Assertion, Endpoint, and ImmediateAssert to WildcardFilter
set WildcardFilter "Variable Constant Generic Parameter SpecParam Memory Assertion Endpoint CellInternal ImmediateAssert"

# Add ignore files for coverage if it's necessary

vsim -assertdebug -coverage -cvgperinstance +nowarnTFMPC $top_opt -msgmode both
# add wave -group "Top" /$top/*
add wave -group "Top DUT" /$top/dut/*
add wave -group "Top FSM" /$top/dut/fsm/*
add wave -group "OBI BUS" /$top/obi_bus_debug_inst/*
add wave -group "Register Interface" /$top/reg_inf_debug_inst/*
add wave -group "Main" /$top/dut/main/*
add wave -group "Main FSM" /$top/dut/main/fsm/*
add wave -group "OBI Memory" /$top/dut/obi_mem/*


view cover
view assertion