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


virtual class abstract_ignore_ctrl_writes extends multi_field_post_predict;

  protected const ctrl_reg CTRL;


  function new(ctrl_reg CTRL);
    this.CTRL = CTRL;
  endfunction


  protected virtual function void call();
    if (get_kind() != UVM_PREDICT_WRITE)
      return;

    if (is_ignore())
      set_reg_to_prev_value();
  endfunction


  protected pure virtual function bit is_ignore();


  local function void set_reg_to_prev_value();
    set_field_value(CTRL.SHAPE, get_prev_field_value(CTRL.SHAPE));
    set_field_value(CTRL.OPERATION, get_prev_field_value(CTRL.OPERATION));
  endfunction

endclass
