/* verilator lint_off UNOPTFLAT */
/* verilator lint_off WIDTHTRUNC */
/* verilator lint_off WIDTHEXPAND */
/* verilator lint_off WIDTHCONCAT */
module gates (
  input logic[0:0] clk_i,
  input logic[0:0] rst_ni,
  output logic[0:0] _ep_rd_req_ack,
  input logic[0:0] _ep_rd_req_valid,
  input logic[15:0] _ep_rd_req_0,
  output logic[0:0] _ep_hit_valid,
  output logic[7:0] _ep_hit_0,
  output logic[0:0] _ep_miss_valid,
  output logic[0:0] _ep_miss_0,
  output logic[0:0] _ep_wr_req_ack,
  input logic[0:0] _ep_wr_req_valid,
  input logic[23:0] _ep_wr_req_0
);
  logic[255:0] mem_q;
  logic[351:0] tag_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin : _proc_transition
    if (~rst_ni) begin
    end
  end
  logic[8:0] thread_0_wire$31;
  logic[8:0] thread_0_wire$29;
  logic[7:0] thread_0_wire$27;
  logic[7:0] thread_0_wire$25;
  logic[7:0] thread_0_wire$23;
  logic[9:0] thread_0_wire$22;
  logic[9:0] thread_0_wire$20;
  logic[8:0] thread_0_wire$18;
  logic[8:0] thread_0_wire$16;
  logic[10:0] thread_0_wire$14;
  logic[15:0] thread_0_wire$13;
  logic[4:0] thread_0_wire$12;
  logic[15:0] thread_0_wire$11;
  logic[23:0] thread_0_wire$10;
  logic[0:0] thread_0_wire$9;
  logic[7:0] thread_0_wire$8;
  logic[255:0] thread_0_wire$7;
  logic[0:0] thread_0_wire$6;
  logic[10:0] thread_0_wire$5;
  logic[351:0] thread_0_wire$4;
  logic[10:0] thread_0_wire$3;
  logic[4:0] thread_0_wire$2;
  logic[15:0] thread_0_wire$1;
  logic[0:0] thread_0_wire$0;
  assign thread_0_wire$0 = _ep_rd_req_valid;
  assign thread_0_wire$1 = _ep_rd_req_0;
  assign thread_0_wire$2 = thread_0_wire$1[0 +: 5];
  assign thread_0_wire$3 = thread_0_wire$1[5 +: 11];
  assign thread_0_wire$4 = tag_q;
  assign thread_0_wire$5 = thread_0_wire$4[thread_0_wire$7 +: 11];
  assign thread_0_wire$6 = thread_0_wire$3 == thread_0_wire$5;
  assign thread_0_wire$7 = mem_q;
  assign thread_0_wire$8 = thread_0_wire$7[thread_0_wire$10 +: 8];
  assign thread_0_wire$9 = _ep_wr_req_valid;
  assign thread_0_wire$10 = _ep_wr_req_0;
  assign thread_0_wire$11 = thread_0_wire$10[8 +: 16];
  assign thread_0_wire$12 = thread_0_wire$11[0 +: 5];
  assign thread_0_wire$13 = thread_0_wire$10[8 +: 16];
  assign thread_0_wire$14 = thread_0_wire$13[5 +: 11];
  localparam logic[3:0] thread_0_wire$15 = 4'd0;
  assign thread_0_wire$16 = {thread_0_wire$15, thread_0_wire$12};
  localparam logic[8:0] thread_0_wire$17 = 9'd11;
  assign thread_0_wire$18 = thread_0_wire$16 * thread_0_wire$17;
  localparam logic[0:0] thread_0_wire$19 = 1'd0;
  assign thread_0_wire$20 = {thread_0_wire$19, thread_0_wire$18};
  localparam logic[9:0] thread_0_wire$21 = 10'd0;
  assign thread_0_wire$22 = thread_0_wire$20 + thread_0_wire$21;
  assign thread_0_wire$23 = thread_0_wire$10[0 +: 8];
  localparam logic[2:0] thread_0_wire$24 = 3'd0;
  assign thread_0_wire$25 = {thread_0_wire$24, thread_0_wire$12};
  localparam logic[7:0] thread_0_wire$26 = 8'd8;
  assign thread_0_wire$27 = thread_0_wire$25 * thread_0_wire$26;
  localparam logic[0:0] thread_0_wire$28 = 1'd0;
  assign thread_0_wire$29 = {thread_0_wire$28, thread_0_wire$27};
  localparam logic[8:0] thread_0_wire$30 = 9'd0;
  assign thread_0_wire$31 = thread_0_wire$29 + thread_0_wire$30;
  for (genvar i = 0; i < 6; i ++) begin : EVENTS0
    logic event_current;
    end
  logic _init_0;
  logic _thread_0_event_counter_5_1_q, _thread_0_event_counter_5_1_n;
  assign EVENTS0[5].event_current = _thread_0_event_counter_5_1_q;
  assign _thread_0_event_counter_5_1_n = EVENTS0[0].event_current;
  assign EVENTS0[4].event_current = EVENTS0[3].event_current && thread_0_wire$6;
  assign EVENTS0[3].event_current = EVENTS0[0].event_current && thread_0_wire$0;
  assign EVENTS0[2].event_current = EVENTS0[1].event_current && thread_0_wire$9;
  assign EVENTS0[1].event_current = EVENTS0[0].event_current && !thread_0_wire$0;
  assign EVENTS0[0].event_current = _init_0 || EVENTS0[5].event_current;
  assign _ep_rd_req_ack = EVENTS0[3].event_current;
  assign _ep_wr_req_ack = EVENTS0[2].event_current;
  assign _ep_hit_valid = EVENTS0[4].event_current;
  assign _ep_hit_0 = thread_0_wire$8;
  always_ff @(posedge clk_i or negedge rst_ni) begin : _thread_0_st_transition
    if (~rst_ni) begin
      _init_0 <= 1'b1;
      mem_q <= '0;
      tag_q <= '0;
      _thread_0_event_counter_5_1_q <= '0;
    end else begin
      if (EVENTS0[4].event_current) begin
      end
      if (EVENTS0[3].event_current) begin
      end
      if (EVENTS0[2].event_current) begin
        mem_q[thread_0_wire$31 +: 8] <= thread_0_wire$23;
        tag_q[thread_0_wire$22 +: 11] <= thread_0_wire$14;
      end
      _init_0 <= 1'b0;
      _thread_0_event_counter_5_1_q <= _thread_0_event_counter_5_1_n;
    end
  end
endmodule
