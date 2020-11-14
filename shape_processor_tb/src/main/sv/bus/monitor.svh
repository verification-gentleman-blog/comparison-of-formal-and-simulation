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


class monitor extends uvm_monitor;

  uvm_analysis_port #(transaction) aport;

  local virtual bus_interface intf;


  function new(string name, uvm_component parent);
    super.new(name, parent);

    aport = new("aport", this);
  endfunction


  function void set_intf(virtual bus_interface intf);
    this.intf = intf;
  endfunction


  virtual task run_phase(uvm_phase phase);
    forever begin
      transaction t;
      collect(t);

      if (t == null)
        continue;

      `uvm_info("DRV", $sformatf("Collected an item:\n%s", t.sprint()), UVM_MEDIUM)
      aport.write(t);
    end
  endtask


  local task collect(output transaction t);
    @(posedge intf.clk);

    if (!intf.read && !intf.write)
      return;

    if (intf.read && intf.write)
      `uvm_fatal("MONERR", "Expected a read or a write cycle, but not both")

    t = transaction::type_id::create("transaction");
    t.direction = intf.read ? transaction::READ : transaction::WRITE;
    t.data = intf.read ? intf.read_data : intf.write_data;
  endtask


  `uvm_component_utils(bus::monitor)

endclass
