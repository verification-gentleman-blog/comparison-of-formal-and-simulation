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


module shape_processor_props(
    input bit rst_n,
    input bit clk,

    input bit write,
    input bit [31:0] write_data,

    input bit read,
    input bit [31:0] read_data,

    input bit error
    );

  default disable iff !rst_n;

  default clocking @(posedge clk);
  endclocking


  typedef struct packed {
    bit [13:0] reserved1;
    bit [1:0] SHAPE;
    bit [10:0] reserved0;
    bit [4:0] OPERATION;
  } ctrl_sfr_reg;


  typedef enum bit [1:0] {
    RECTANGLE = 'b01,
    TRIANGLE = 'b10
  } shape_e;

  typedef enum bit [4:0] {
    PERIMETER = 'b00_000,
    AREA = 'b00_001,
    IS_SQUARE = 'b01_000,
    IS_EQUILATERAL = 'b10_000,
    IS_ISOSCELES = 'b10_001
  } operation_e;


  ctrl_sfr_reg write_data_as_ctrl_sfr;
  assign write_data_as_ctrl_sfr = write_data;


  legal_write_data_written_to_shape: assert property (
      write && is_legal_ctrl_write_data() |=>
          shape_processor.ctrl_sfr.shape == $past(write_data_as_ctrl_sfr.SHAPE));


  function bit is_legal_ctrl_write_data();
    return is_legal_shape(write_data_as_ctrl_sfr.SHAPE) &&
        is_legal_operation(write_data_as_ctrl_sfr.OPERATION);
  endfunction

  function bit is_legal_shape(bit [1:0] val);
    return val inside { RECTANGLE, TRIANGLE };
  endfunction

  function bit is_legal_operation(bit [4:0] val);
    return val inside { PERIMETER, AREA, IS_SQUARE, IS_EQUILATERAL, IS_ISOSCELES };
  endfunction


  write_data_written_to_operation: assert property (
      write && is_legal_ctrl_write_data() |=>
          shape_processor.ctrl_sfr.operation == $past(write_data_as_ctrl_sfr.OPERATION));


  ctrl_sfr_constant_if_no_write: assert property (
      !write |=> $stable(shape_processor.ctrl_sfr)
      );


  ctrl_sfr_constant_if_illegal_shape_write: assert property (
      write && !is_legal_shape(write_data_as_ctrl_sfr.SHAPE) |=>
          $stable(shape_processor.ctrl_sfr));

  ctrl_sfr_constant_if_illegal_operation_write: assert property (
      write && !is_legal_operation(write_data_as_ctrl_sfr.OPERATION) |=>
          $stable(shape_processor.ctrl_sfr));

endmodule


bind shape_processor shape_processor_props props(.*);
