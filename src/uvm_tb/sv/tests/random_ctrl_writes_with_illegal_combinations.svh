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


class random_ctrl_writes_with_illegal_combinations extends abstract_test;

  typedef class test_sequence;


  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction


  virtual function void start_of_simulation_phase(uvm_phase phase);
    super.start_of_simulation_phase(phase);

    uvm_config_db #(uvm_object_wrapper)::set(
        vsequencer,
        "main_phase",
        "default_sequence",
        test_sequence::get_type());
  endfunction


  class write_ctrl_sequence extends uvm_sequence;

    rand shape_e shape;
    rand operation_e operation;

    constraint no_keep {
      shape != KEEP_SHAPE;
      operation != KEEP_OPERATION;
    }

    constraint no_generic_operations {
      !(operation inside { PERIMETER, AREA });
    }

    constraint not_rectangle_when_rectangle_only_operation {
      if (operation inside { IS_SQUARE })
        shape != RECTANGLE;
    }

    constraint not_triangle_when_triangle_only_operation {
      if (operation inside { IS_EQUILATERAL, IS_ISOSCELES })
        shape != TRIANGLE;
    }

    function new(string name = get_type_name());
      super.new(name);
    endfunction

    virtual task body();
      p_sequencer.regs.CTRL.SHAPE.set(shape);
      p_sequencer.regs.CTRL.OPERATION.set(operation);
      `write_reg(p_sequencer.regs.CTRL)
      `read_reg(p_sequencer.regs.CTRL)
    endtask

    `uvm_object_utils(write_ctrl_sequence)
    `uvm_declare_p_sequencer(virtual_sequencer)

  endclass


  class test_sequence extends uvm_sequence;

    function new(string name = get_type_name());
      super.new(name);
      set_automatic_phase_objection(1);
    endfunction

    virtual task body();
      repeat (10) begin
        write_ctrl_sequence write_ctrl;
        `uvm_do(write_ctrl)
      end
    endtask

    `uvm_object_utils(test_sequence)
    `uvm_declare_p_sequencer(virtual_sequencer)

  endclass


  `uvm_component_utils(random_ctrl_writes_with_illegal_combinations)

endclass
