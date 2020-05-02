$ROOT/src/dut/sv/shape_processor.sv

-makelib worklib
  -incdir $ROOT/src/uvm_tb/sv/tests
  $ROOT/src/uvm_tb/sv/tests/shape_processor_tests.sv
-endlib

$ROOT/src/uvm_tb/sv/shape_processor_tb_top.sv
