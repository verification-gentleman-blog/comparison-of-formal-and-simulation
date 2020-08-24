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


class reg_block extends uvm_reg_block;

  rand ctrl_reg CTRL;


  function new(string name = get_type_name());
    super.new(name);

    CTRL = ctrl_reg::type_id::create("CTRL");
    CTRL.configure(this);

    default_map = create_map("default_map", 'h0, 4, UVM_LITTLE_ENDIAN);
    default_map.add_reg(CTRL, 'h0, "RW");
  endfunction


  `uvm_object_utils(shape_processor_regs::reg_block)

endclass
