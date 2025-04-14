//////////////////////////////////////////////////
// Title:   assertions_hdlc
// Author:  
// Date:    
//////////////////////////////////////////////////

/* The assertions_hdlc module is a test module containing the concurrent
   assertions. It is used by binding the signals of assertions_hdlc to the
   corresponding signals in the test_hdlc testbench. This is already done in
   bind_hdlc.sv 

   For this exercise you will write concurrent assertions for the Rx module:
   - Verify that Rx_FlagDetect is asserted two cycles after a flag is received
   - Verify that Rx_AbortSignal is asserted after receiving an abort flag
*/

module assertions_hdlc (
  output int   ErrCntAssertions,
  input  logic Clk,
  input  logic Rst,
  input  logic Rx,
  input  logic Rx_FlagDetect,
  input  logic Rx_ValidFrame,
  input  logic Rx_AbortDetect,
  input  logic Rx_AbortSignal,
  input  logic Rx_Overflow,
  input  logic Rx_WrBuff,
  input  logic Rx_EoF,
  input  logic Rx_NewByte,
  input  logic [7:0] Rx_FrameSize
);

  initial begin
    ErrCntAssertions  =  0;
  end

  /*******************************************
   *  Verify correct Rx_FlagDetect behavior  *
   *******************************************/

  sequence Rx_flag;
    // INSERT CODE HERE
    @(posedge Clk) (Rx_FlagDetect); 
  endsequence

  // Check if flag sequence is detected
  property RX_FlagDetect;
    @(posedge Clk) disable iff (Rst)
    ##2 (Rx_flag); //DOUBLE CHECK
  endproperty

  RX_FlagDetect_Assert : assert property (RX_FlagDetect) begin
    $display("PASS: Flag detect");
  end else begin 
    $error("Flag sequence did not generate FlagDetect"); 
    ErrCntAssertions++; 
  end

  /********************************************
   *  Verify correct Rx_AbortSignal behavior  *
   ********************************************/

  //If abort is detected during valid frame. then abort signal should go high
  property RX_AbortSignal;
    // INSERT CODE HERE
    @(posedge Clk) disable iff (Rst)
    ##1 ((Rx_AbortDetect)) |=> Rx_AbortSignal;
    //@(posedge Clk) Rx_AbortDetect |=> Rx_AbortSignal;
  endproperty

  RX_AbortSignal_Assert : assert property (RX_AbortSignal) begin
    $display("PASS: Abort signal");
  end else begin 
    $error("AbortSignal did not go high after AbortDetect during validframe"); 
    ErrCntAssertions++; 
  end

  //12. When a whole RX frame has been received, check if end of frame is generated.
  property RX_EndOfFrame;
    @(posedge Clk) disable iff (!Rst)
    Rx_ValidFrame == 1 ##1 Rx_ValidFrame == 0 |=> $rose(Rx_EoF);
	endproperty

  RX_EndOfFrame_Assert : assert property (RX_EndOfFrame) begin
    $display("PASS: End Of Frame signal");
  end else begin 
    $error("End Of Frame signal did not go high after Rx_ValidFrame went low"); 
    ErrCntAssertions++; 
  end

  //13. When receiving more than 128 bytes, Rx Overflow should be asserted.
  property RX_Overflow;
    @(posedge Clk) disable iff (!Rst || !Rx_ValidFrame)
    //Rx_ValidFrame == 0 ##1 Rx_ValidFrame == 1 ##0 Rx_NewByte == 0 ##1 Rx_ValidFrame == 1 [->129] |=> $rose(Rx_Overflow)
    $rose(Rx_ValidFrame) ##0 ($rose(Rx_NewByte) [->129]) |=> $rose(Rx_Overflow)
  endproperty

  RX_Overflow_Assert : assert property (RX_Overflow) begin
    $display("PASS: RX_Overflow detected afrer more than 128 bytes received");
  end else begin
    $error("RX_Overflow did not go high after receiving more than 128 bytes");
    ErrCntAssertions++;
  end

  logic [7:0] byte_counter; // Counter to track the number of bytes received

  // Update the byte counter
  always_ff @(posedge Clk or negedge Rst) begin
    if (!Rst) begin
      byte_counter <= 8'd0;
    end else if (!Rx_ValidFrame) begin
      byte_counter <= 8'd0; // Reset the counter when not in a valid frame
    end else if ($rose(Rx_NewByte)) begin
      byte_counter <= byte_counter + 1; // Increment the counter on each new byte
    end
  end

  // 14. Rx_FrameSize should equal the exact number of bytes received in a frame (max. 126 bytes).
  property RX_FrameSize_Exact;
    @(posedge Clk) disable iff (!Rst)
    $fell(Rx_ValidFrame) |-> (Rx_FrameSize == byte_counter);
  endproperty

  RX_FrameSize_Exact_Assert : assert property (RX_FrameSize_Exact) begin
    $display("PASS: Rx_FrameSize matches the exact number of bytes received.");
  end else begin
    $error("FAIL: Rx_FrameSize does not match the exact number of bytes received. Expected: %0d, Got: %0d", byte_counter, Rx_FrameSize);
    ErrCntAssertions++;
  end

endmodule
