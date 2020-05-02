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


`define write_reg(REG) \
   begin \
     uvm_pkg::uvm_status_e status; \
     REG.write(status, REG.get()); \
   end


`define read_reg(REG) \
   begin \
     uvm_pkg::uvm_status_e status; \
     uvm_pkg::uvm_reg_data_t data; \
     REG.read(status, data); \
   end
