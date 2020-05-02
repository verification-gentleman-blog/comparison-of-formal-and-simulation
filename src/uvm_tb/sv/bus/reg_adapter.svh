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


class reg_adapter extends uvm_reg_adapter;

  function new(string name = get_type_name());
    super.new(name);
  endfunction


  virtual function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);
    transaction reg_transaction = transaction::type_id::create("reg_transaction");

    // TODO Implement

    return reg_transaction;
  endfunction


  virtual function void bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
    transaction bus_transaction;
    if (!$cast(bus_transaction, bus_item))
      `uvm_fatal("CASTERR", "Cast error")

    // TODO Implement
  endfunction


  `uvm_object_utils(bus::reg_adapter)

endclass
