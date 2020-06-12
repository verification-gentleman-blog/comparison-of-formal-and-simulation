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


class ignore_ctrl_writes_with_illegal_combination extends multi_field_post_predict;

  local const ctrl_reg CTRL;


  function new(ctrl_reg CTRL);
    this.CTRL = CTRL;
  endfunction


  // XXX WORKAROUND Xcelium doesn't support scoped constructor calls.
  static function ignore_ctrl_writes_with_illegal_combination new_instance(ctrl_reg CTRL);
    new_instance = new(CTRL);
  endfunction


  protected virtual function void call();
    shape_e shape;
    operation_e operation;

    if (!$cast(shape, get_field_value(CTRL.SHAPE)))
      return;
    if (!$cast(operation, get_field_value(CTRL.OPERATION)))
      return;

    if (is_illegal(shape, operation)) begin
      set_field_value(CTRL.SHAPE, get_prev_field_value(CTRL.SHAPE));
      set_field_value(CTRL.OPERATION, get_prev_field_value(CTRL.OPERATION));
    end
  endfunction


  local function bit is_illegal(shape_e shape, operation_e operation);
    if (is_rectangle_only_operation(operation) && shape != RECTANGLE)
      return 1;
    if (is_triangle_only_operation(operation) && shape != TRIANGLE)
      return 1;
    return 0;
  endfunction


  local function bit is_rectangle_only_operation(operation_e operation);
    return operation inside { IS_SQUARE };
  endfunction


  local function bit is_triangle_only_operation(operation_e operation);
    return operation inside { IS_EQUILATERAL, IS_ISOSCELES };
  endfunction

endclass
