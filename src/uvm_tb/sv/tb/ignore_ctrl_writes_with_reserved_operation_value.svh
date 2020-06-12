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


class ignore_ctrl_writes_with_reserved_operation_value extends multi_field_post_predict;

  local const ctrl_reg CTRL;


  function new(ctrl_reg CTRL);
    this.CTRL = CTRL;
  endfunction


  // XXX WORKAROUND Xcelium doesn't support scoped constructor calls.
  static function ignore_ctrl_writes_with_reserved_operation_value new_instance(ctrl_reg CTRL);
    new_instance = new(CTRL);
  endfunction


  protected virtual function void call();
    operation_e dummy;

    if (get_kind() != UVM_PREDICT_WRITE)
      return;

    if (!$cast(dummy, get_field_value(CTRL.OPERATION))) begin
      set_field_value(CTRL.SHAPE, get_prev_field_value(CTRL.SHAPE));
      set_field_value(CTRL.OPERATION, get_prev_field_value(CTRL.OPERATION));
    end
  endfunction

endclass
