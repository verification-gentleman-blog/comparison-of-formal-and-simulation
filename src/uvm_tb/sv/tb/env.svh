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


class env extends uvm_env;

  bus::agent agent;
  shape_processor_regs::reg_block regs;


  function new(string name, uvm_component parent);
    super.new(name, parent);

    regs = shape_processor_regs::reg_block::type_id::create("regs");
    regs.lock_model();
  endfunction


  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    agent = bus::agent::type_id::create("agent", this);
  endfunction


  virtual function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);

    regs.default_map.set_sequencer(agent.sequencer, agent.reg_adapter);
  endfunction


  `uvm_component_utils(shape_processor_tb::env)

endclass
