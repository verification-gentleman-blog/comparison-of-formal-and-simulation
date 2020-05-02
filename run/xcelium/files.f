$ROOT/src/dut/sv/shape_processor.sv

-makelib worklib
  -incdir $ROOT/src/uvm_tb/sv/bus
  $ROOT/src/uvm_tb/sv/bus/bus.sv
  $ROOT/src/uvm_tb/sv/bus/bus_interface.sv
-endlib

-makelib worklib
  -incdir $ROOT/src/uvm_tb/sv/regs
  $ROOT/src/uvm_tb/sv/regs/shape_processor_regs.sv
-endlib

-makelib worklib
  -incdir $ROOT/src/uvm_tb/sv/tb
  $ROOT/src/uvm_tb/sv/tb/shape_processor_tb.sv
-endlib

-makelib worklib
  -incdir $ROOT/src/uvm_tb/sv/tests
  $ROOT/src/uvm_tb/sv/tests/shape_processor_tests.sv
-endlib

$ROOT/src/uvm_tb/sv/shape_processor_tb_top.sv
