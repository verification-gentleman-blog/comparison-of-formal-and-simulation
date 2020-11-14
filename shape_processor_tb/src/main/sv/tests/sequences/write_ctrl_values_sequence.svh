// Copyright 2020 Tudor Timisescu (verificationgentleman.com)
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.


class write_ctrl_values_sequence extends uvm_sequence;

  rand shape_e shape;
  rand operation_e operation;


  function new(string name = get_type_name());
    super.new(name);
  endfunction


  virtual task body();
    p_sequencer.regs.CTRL.SHAPE.set(shape);
    p_sequencer.regs.CTRL.OPERATION.set(operation);
    `write_reg(p_sequencer.regs.CTRL)
  endtask


  `uvm_object_utils(write_ctrl_values_sequence)
  `uvm_declare_p_sequencer(virtual_sequencer)
  `constraints_utils(write_ctrl_values_sequence)

endclass
