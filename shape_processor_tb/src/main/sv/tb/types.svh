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


typedef enum bit [2:0] {
  CIRCLE = 'b001,
  RECTANGLE = 'b010,
  TRIANGLE = 'b100,
  KEEP_SHAPE = '1
} shape_e;

typedef enum bit [6:0] {
  PERIMETER = 'b000_0000,
  AREA = 'b000_0001,
  IS_SQUARE = 'b010_0000,
  IS_EQUILATERAL = 'b100_0000,
  IS_ISOSCELES = 'b100_0001,
  KEEP_OPERATION = '1
} operation_e;
