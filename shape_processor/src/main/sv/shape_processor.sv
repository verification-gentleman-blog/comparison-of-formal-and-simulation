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
    bit [2:0] shape;
    bit [6:0] operation;
  } ctrl_sfr;


  bit [2:0] new_shape;

  always_comb
    if (write_data[18:16] == '1)
      new_shape = ctrl_sfr.shape;
    else
      new_shape = write_data[18:16];


  bit [6:0] new_operation;

  always_comb
    if (write_data[6:0] == '1)
      new_operation = ctrl_sfr.operation;
    else
      new_operation = write_data[6:0];


  always_ff @(posedge clk or negedge rst_n)
    if (!rst_n) begin
      ctrl_sfr.shape <= 'b001;
      ctrl_sfr.operation <= 'b000_0000;
    end
    else begin
      if (write) begin
        if (is_legal_shape(new_shape)
            && is_legal_operation(new_operation)
            && is_legal_combination(new_shape, new_operation)) begin
          ctrl_sfr.shape <= new_shape;
          ctrl_sfr.operation <= new_operation;
        end
      end
    end


  function bit is_legal_shape(bit [2:0] val);
    return $onehot(val);
  endfunction


  function bit is_legal_operation(bit [6:0] val);
    case (val[6:4])
      'b000:
        return val[3:0] inside { 0, 1 };
      'b010:
        return val[3:0] == 0;
      'b100:
        return val[3:0] inside { 0, 1 };
    endcase
    return 0;
  endfunction


  function bit is_legal_combination(bit [2:0] shape, bit [6:0] operation);
    if (operation[6:4] == 0)
      return 1;
    return operation[6:4] == shape;
  endfunction


  always_comb begin
    read_data = '0;
    read_data[18:16] = ctrl_sfr.shape;
    read_data[6:0] = ctrl_sfr.operation;
  end

endmodule
