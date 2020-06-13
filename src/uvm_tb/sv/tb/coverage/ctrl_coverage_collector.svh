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


class ctrl_coverage_collector extends uvm_subscriber #(uvm_reg_item);

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction


  virtual function void write(uvm_reg_item t);
    ctrl_reg CTRL;

    // We'll be covering at write accesses, even though this isn't that cool from a methodological
    // point of view, because it doesn't propagate its effect to outputs.
    if (t.kind != UVM_WRITE)
      return;

    if (!$cast(CTRL, t.element))
      return;

    `uvm_info("DBG", $sformatf("Collecting coverage from %s", t.convert2string()), UVM_NONE)
  endfunction

endclass
