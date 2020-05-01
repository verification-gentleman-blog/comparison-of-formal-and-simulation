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


  ctrl_sfr_reg write_data_as_ctrl_sfr;
  assign write_data_as_ctrl_sfr = write_data;


  write_data_written_to_shape: assert property (
      write |=> shape_processor.ctrl_sfr.shape == $past(write_data_as_ctrl_sfr.SHAPE)
      );

  write_data_written_to_operation: assert property (
      write |=> shape_processor.ctrl_sfr.operation == $past(write_data_as_ctrl_sfr.OPERATION)
      );

  ctrl_sfr_constant_if_no_write: assert property (
      !write |=> $stable(shape_processor.ctrl_sfr)
      );

endmodule


bind shape_processor shape_processor_props props(.*);
