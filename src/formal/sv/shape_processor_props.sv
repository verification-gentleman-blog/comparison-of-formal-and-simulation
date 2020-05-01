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

  import shape_processor_modeling::*;


  default disable iff !rst_n;

  default clocking @(posedge clk);
  endclocking


  only_legal_shapes_in_ctrl_sfr: assert property (
      is_legal_shape(shape_processor.ctrl_sfr.shape));

  only_legal_operations_in_ctrl_sfr: assert property (
      is_legal_operation(shape_processor.ctrl_sfr.operation));


  ctrl_sfr_reg write_data_as_ctrl_sfr;
  assign write_data_as_ctrl_sfr = write_data;


  legal_write_data_written_to_shape: assert property (
      write && is_legal_ctrl_write_data() |=>
          shape_processor.ctrl_sfr.shape == $past(write_data_as_ctrl_sfr.SHAPE));


  function bit is_legal_ctrl_write_data();
    return is_legal_shape(write_data_as_ctrl_sfr.SHAPE)
        && is_legal_operation(write_data_as_ctrl_sfr.OPERATION)
        && is_legal_combination(write_data_as_ctrl_sfr.SHAPE, write_data_as_ctrl_sfr.OPERATION);
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

  ctrl_sfr_constant_if_illegal_combination_write: assert property (
      write && !is_legal_write_data_combination() |=>
          $stable(shape_processor.ctrl_sfr));


  function bit is_legal_write_data_combination();
    return
        is_legal_combination(write_data_as_ctrl_sfr.SHAPE, write_data_as_ctrl_sfr.OPERATION);
  endfunction

endmodule


bind shape_processor shape_processor_props props(.*);
