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


class driver extends uvm_driver #(transaction);

  local virtual bus_interface intf;


  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction


  function void set_intf(virtual bus_interface intf);
    this.intf = intf;
  endfunction


  virtual task run_phase(uvm_phase phase);
    forever begin
      seq_item_port.get_next_item(req);

      `uvm_info("DRV", $sformatf("Got an item:\n%s", req.sprint()), UVM_MEDIUM)

      if (intf.clk == 0)
        @(posedge intf.clk);

      drive(req);

      seq_item_port.item_done();
    end
  endtask


  local task drive(transaction t);
    case (t.direction)
      transaction::READ:
        intf.read <= 1;
      transaction::WRITE:
        intf.write <= 1;
      default:
        `uvm_fatal("CASERR", "Unkown direction")
    endcase

    if (t.direction == transaction::WRITE)
      intf.write_data <= t.data;

    @(posedge intf.clk);

    intf.read <= 0;
    intf.write <= 0;

    if (t.direction == transaction::READ)
      t.data = intf.read_data;
  endtask


  `uvm_component_utils(bus::driver)

endclass
