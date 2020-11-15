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


package shape_processor_modeling;

  typedef struct packed {
    bit [13:0] reserved1;
    bit [1:0] SHAPE;
    bit [9:0] reserved0;
    bit [5:0] OPERATION;
  } ctrl_sfr_reg;


  typedef enum bit [1:0] {
    RECTANGLE = 'b01,
    TRIANGLE = 'b10,
    KEEP_SHAPE = '1
  } shape_e;

  typedef enum bit [5:0] {
    PERIMETER = 'b00_0000,
    AREA = 'b00_0001,
    IS_SQUARE = 'b01_0000,
    IS_EQUILATERAL = 'b10_0000,
    IS_ISOSCELES = 'b10_0001,
    KEEP_OPERATION = '1
  } operation_e;


  function bit is_reserved_shape(bit [1:0] val);
    return !(val inside { KEEP_SHAPE, RECTANGLE, TRIANGLE });
  endfunction


  function bit is_reserved_operation(bit [5:0] val);
    return !(val inside
        { KEEP_OPERATION, PERIMETER, AREA, IS_SQUARE, IS_EQUILATERAL, IS_ISOSCELES });
  endfunction


  function bit is_legal_combination(shape_e shape, operation_e operation);
    if (shape == KEEP_SHAPE)
      return 0;
    if (operation == KEEP_OPERATION)
      return 0;

    if (operation inside { PERIMETER, AREA })
      return 1;
    if (operation == IS_SQUARE)
      return shape == RECTANGLE;
    if (operation inside { IS_EQUILATERAL, IS_ISOSCELES })
      return shape == TRIANGLE;
    return 0;
  endfunction

endpackage
