set root $::env(ROOT)

set_mode setup
read_verilog -sv $root/shape_processor/src/main/sv/shape_processor.sv
elaborate
compile

set_mode mv
read_sva \
    $root/shape_processor_props/src/main/sv/shape_processor_modeling.sv \
    $root/shape_processor_props/src/main/sv/shape_processor_props.sv
