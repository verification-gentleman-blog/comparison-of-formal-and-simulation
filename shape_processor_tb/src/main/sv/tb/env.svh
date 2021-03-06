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
  uvm_reg_predictor #(bus::transaction) reg_predictor;
  ctrl_coverage_collector ctrl_cov_collector;
  ctrl_keep_operation_coverage_collector ctrl_keep_operation_cov_collector;
  ctrl_keep_both_coverage_collector ctrl_keep_both_cov_collector;


  function new(string name, uvm_component parent);
    super.new(name, parent);

    regs = shape_processor_regs::reg_block::type_id::create("regs");
    regs.lock_model();

    uvm_reg_field_cb::add(regs.CTRL.SHAPE, keep_shape::new_instance());
    uvm_reg_field_cb::add(regs.CTRL.OPERATION, keep_operation::new_instance());

    multi_field_post_predict::add(
        ignore_ctrl_writes_with_reserved_shape_value::new_instance(regs.CTRL),
        regs.CTRL);
    multi_field_post_predict::add(
        ignore_ctrl_writes_with_reserved_operation_value::new_instance(regs.CTRL),
        regs.CTRL);

    multi_field_post_predict::add(
        ignore_ctrl_writes_with_illegal_combination::new_instance(regs.CTRL),
        regs.CTRL);
  endfunction


  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    agent = bus::agent::type_id::create("agent", this);
    reg_predictor = uvm_reg_predictor #(bus::transaction)::type_id::create("reg_predictor", this);
    ctrl_cov_collector = new("ctrl_cov_collector", this);
    ctrl_keep_operation_cov_collector = new("ctrl_keep_operation_cov_collector", this, regs.CTRL);
    ctrl_keep_both_cov_collector = new("ctrl_keep_both_cov_collector", this, regs.CTRL);
  endfunction


  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);

    agent.monitor.aport.connect(reg_predictor.bus_in);
    reg_predictor.reg_ap.connect(ctrl_cov_collector.analysis_export);
    reg_predictor.reg_ap.connect(ctrl_keep_operation_cov_collector.analysis_export);
    reg_predictor.reg_ap.connect(ctrl_keep_both_cov_collector.analysis_export);
  endfunction


  virtual function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);

    regs.default_map.set_sequencer(agent.sequencer, agent.reg_adapter);

    reg_predictor.map = regs.default_map;
    reg_predictor.adapter = agent.reg_adapter;

    regs.default_map.set_auto_predict(0);
    regs.default_map.set_check_on_read();
  endfunction


  virtual function void start_of_simulation_phase(uvm_phase phase);
    super.start_of_simulation_phase(phase);

    regs.reset();
  endfunction


  `uvm_component_utils(shape_processor_tb::env)

endclass
