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


class virtual_sequencer extends uvm_virtual_sequencer;

  const shape_processor_regs::reg_block regs;


  function new(string name, uvm_component parent, shape_processor_regs::reg_block regs);
    super.new(name, parent);
    this.regs = regs;
  endfunction

endclass
