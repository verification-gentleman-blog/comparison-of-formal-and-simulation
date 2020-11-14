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


class random_ctrl_writes_with_reserved_shape_values extends abstract_test;

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

    /* local */ typedef shape_processor_tb::shape_e queue_of_shape_e[$];

    local static const shape_processor_tb::shape_e ALL_SHAPE_VALUES[] = get_all_shape_values();

    local static function queue_of_shape_e get_all_shape_values();
      queue_of_shape_e result;
      shape_processor_tb::shape_e val = val.first();
      forever begin
        result.push_back(val);// ... do stuff in iteration
        if (val == val.last())
          break;
        val = val.next();
      end
      return result;
    endfunction

    function new(string name = get_type_name());
      super.new(name);
    endfunction

    virtual task body();
      if (!p_sequencer.regs.CTRL.randomize() with {
        !(SHAPE.value inside { ALL_SHAPE_VALUES });
      })
        `uvm_fatal("RANDERR", "Randomization error")
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


  `uvm_component_utils(random_ctrl_writes_with_reserved_shape_values)

endclass
