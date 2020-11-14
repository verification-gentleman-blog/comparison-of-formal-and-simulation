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


class legal_ctrl_values_constraint extends abstract_constraint #(write_ctrl_values_sequence);

  constraint no_keep {
    object.shape != KEEP_SHAPE;
    object.operation != KEEP_OPERATION;
  }

  constraint rectangle_when_rectangle_only_operation {
    if (object.operation inside { IS_SQUARE })
      object.shape == RECTANGLE;
  }

  constraint triangle_when_triangle_only_operation {
    if (object.operation inside { IS_EQUILATERAL, IS_ISOSCELES })
      object.shape == TRIANGLE;
  }


  // XXX WORKAROUND Xcelium doesn't support scoped constructor calls.
  static function legal_ctrl_values_constraint new_instance();
    new_instance = new();
  endfunction

endclass
