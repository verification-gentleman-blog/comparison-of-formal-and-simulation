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


module shape_processor(
    input bit rst_n,
    input bit clk,

    input bit write,
    input bit [31:0] write_data,

    input bit read,
    output bit [31:0] read_data,

    output bit error
    );

  struct {
    bit [1:0] shape;
    bit [4:0] operation;
  } ctrl_sfr;

  always_ff @(posedge clk)
    if (write) begin
      if (is_legal_data(write_data)) begin
        ctrl_sfr.shape <= write_data[17:16];
        ctrl_sfr.operation <= write_data[4:0];
      end
    end


  function bit is_legal_data(bit [31:0] data);
    return $onehot(write_data[17:16])
        && is_legal_operation(write_data[4:0])
        && is_legal_combination(write_data[17:16], write_data[4:0]);
  endfunction


  function bit is_legal_operation(bit [4:0] val);
    case (val[4:3])
      'b00:
        return val[2:0] inside { 0, 1 };
      'b01:
        return val[2:0] == 0;
      'b10:
        return val[2:0] inside { 0, 1 };
    endcase
    return 0;
  endfunction


  function bit is_legal_combination(bit [1:0] shape, bit [4:0] operation);
    if (operation[4:3] == 0)
      return 1;
    return operation[4:3] == shape;
  endfunction

endmodule
