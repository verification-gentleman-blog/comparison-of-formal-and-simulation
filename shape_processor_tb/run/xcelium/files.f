-makelib worklib
  -incdir $ROOT/shape_processor_tb/dependencies/constraints/src/main/sv
  $ROOT/shape_processor_tb/dependencies/constraints/src/main/sv/*.sv
-endlib

-makelib worklib
  -incdir $ROOT/shape_processor_tb/dependencies/uvm-extras/src/main/sv
  $ROOT/shape_processor_tb/dependencies/uvm-extras/src/main/sv/*.sv
-endlib

$ROOT/shape_processor/src/main/sv/shape_processor.sv

-makelib worklib
  -incdir $ROOT/shape_processor_tb/src/main/sv/bus
  $ROOT/shape_processor_tb/src/main/sv/bus/bus.sv
  $ROOT/shape_processor_tb/src/main/sv/bus/bus_interface.sv
-endlib

-makelib worklib
  -incdir $ROOT/shape_processor_tb/src/main/sv/regs
  $ROOT/shape_processor_tb/src/main/sv/regs/shape_processor_regs.sv
-endlib

-makelib worklib
  -incdir $ROOT/shape_processor_tb/src/main/sv/tb
  $ROOT/shape_processor_tb/src/main/sv/tb/shape_processor_tb.sv
-endlib

-makelib worklib
  -incdir $ROOT/shape_processor_tb/dependencies/constraints/src/main/headers
  -incdir $ROOT/shape_processor_tb/src/main/sv/tests
  $ROOT/shape_processor_tb/src/main/sv/tests/shape_processor_tests.sv
-endlib

$ROOT/shape_processor_tb/src/main/sv/shape_processor_tb_top.sv
