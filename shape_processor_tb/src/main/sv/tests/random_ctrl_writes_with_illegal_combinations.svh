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

    write_ctrl_values_sequence::add_global_constraint(
        illegal_combination_of_control_values_constraint::new_instance());
  endfunction


  class test_sequence extends uvm_sequence;

    function new(string name = get_type_name());
      super.new(name);
      set_automatic_phase_objection(1);
    endfunction

    virtual task body();
      repeat (10) begin
        test_ctrl_sequence test_ctrl;
        `uvm_do(test_ctrl)
      end
    endtask

    `uvm_object_utils(test_sequence)
    `uvm_declare_p_sequencer(virtual_sequencer)

  endclass


  `uvm_component_utils(random_ctrl_writes_with_illegal_combinations)

endclass
