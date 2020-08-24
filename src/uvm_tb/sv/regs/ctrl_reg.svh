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


class ctrl_reg extends uvm_reg;

  rand uvm_reg_field SHAPE;
  rand uvm_reg_field OPERATION;


  function new(string name = get_type_name());
    super.new(name, 32, 0);

    SHAPE = uvm_reg_field::type_id::create("SHAPE");
    SHAPE.configure(this, 2, 16, "RW", 0, 'b01, 1, 1, 0);

    OPERATION = uvm_reg_field::type_id::create("OPERATION");
    OPERATION.configure(this, 6, 0, "RW", 0, '0, 1, 1, 0);
  endfunction


  `uvm_object_utils(shape_processor_regs::ctrl_reg)

endclass
