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


class legal_ctrl_value_combinations_coverage;

  covergroup cg with function sample(shape_e shape, operation_e operation);
    option.per_instance = 1;

    coverpoint shape {
      ignore_bins keep = { KEEP_SHAPE };
    }
    coverpoint operation {
      ignore_bins keep = { KEEP_OPERATION };
    }
    cross shape, operation {
      ignore_bins illegal_for_rectangle = binsof (shape) intersect { RECTANGLE }
          && binsof (operation) intersect { IS_EQUILATERAL, IS_ISOSCELES };
      ignore_bins illegal_for_triangle = binsof (shape) intersect { TRIANGLE }
          && binsof (operation) intersect { IS_SQUARE };
    }
  endgroup


  function new();
    cg = new();
  endfunction


  function void sample(uvm_reg_data_t SHAPE, uvm_reg_data_t OPERATION);
    shape_e shape;
    operation_e operation;

    if (!$cast(shape, SHAPE))
      return;
    if (!$cast(operation, OPERATION))
      return;

    cg.sample(shape, operation);
  endfunction

endclass
