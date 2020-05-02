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


class random_ctrl_writes extends abstract_test;

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


  class test_sequence extends uvm_sequence;

    function new(string name = get_type_name());
      super.new(name);
      set_automatic_phase_objection(1);
    endfunction

    virtual task body();
      repeat (10) begin
        if (!p_sequencer.regs.CTRL.randomize())
          `uvm_fatal("RANDERR", "Randomization error")
        `write_reg(p_sequencer.regs.CTRL)
        `read_reg(p_sequencer.regs.CTRL)
      end
    endtask

    `uvm_object_utils(test_sequence)
    `uvm_declare_p_sequencer(virtual_sequencer)

  endclass


  `uvm_component_utils(random_ctrl_writes)

endclass
