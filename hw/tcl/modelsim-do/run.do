onbreak {resume}

# create library
if [file exists work] {
    vdel -all
}
vlib work
 
# compile all source files
vlog gates.v and2.v cache.v memory.v proc.v set.v top.v

#optimize design
vopt +acc top -o top_opt

# Coverage (branch, condition, expression statement, extended toggle, and finite state machine coverage statistics)
# vopt +cover=bcesxf test_sm -o test_sm_opt
# vsim -coverage test_sm_opt


# load simulator with optimized design
vsim top_opt

# set WildcardFilter variables
set WildcardFilter "Variable Constant Generic Parameter SpecParam Memory Assertion Cover Endpoint ScVariable ImmediateAssert VHDLFile"

# wave signals
add wave /top/p/*
add log -r /*

# run simulation
run -all