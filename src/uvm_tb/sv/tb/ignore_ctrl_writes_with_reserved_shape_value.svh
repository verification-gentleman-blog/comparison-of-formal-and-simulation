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


class ignore_ctrl_writes_with_reserved_shape_value extends abstract_ignore_ctrl_writes;

  function new(ctrl_reg CTRL);
    super.new(CTRL);
  endfunction


  // XXX WORKAROUND Xcelium doesn't support scoped constructor calls.
  static function ignore_ctrl_writes_with_reserved_shape_value new_instance(ctrl_reg CTRL);
    new_instance = new(CTRL);
  endfunction


  protected virtual function bit is_ignore();
    shape_e dummy;
    return !$cast(dummy, get_field_value(CTRL.SHAPE));
  endfunction

endclass
