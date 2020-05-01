set root $::env(ROOT)

set_mode setup
read_verilog -sv $root/src/dut/sv/shape_processor.sv
elaborate
compile

set_mode mv
read_sva \
    $root/src/formal/sv/shape_processor_modeling.sv \
    $root/src/formal/sv/shape_processor_props.sv
