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
  input  logic Rx_Ready,
  input  logic Rx_FCSerr,
  input  logic Rx_FCSen,
  input  logic Rx_FrameError,
  input  logic Tx_DataAvail,
  input  logic Tx_Done,
  input  logic Rx_NewByte,
  input  logic [7:0] Rx_FrameSize,
  input  logic Rx_FrameError
);

  initial begin
    ErrCntAssertions  =  0;
  end

  /*******************************************
   *  Verify correct Rx_FlagDetect behavior  *
   *******************************************/

  sequence Rx_flag;
    // INSERT CODE HERE
    @(posedge Clk)   
      !Rx ##1  // 0
      Rx [*6] ##1 // 111111
      !Rx;      // 0
  endsequence

  // Check if flag sequence is detected
  property RX_FlagDetect;
    @(posedge Clk) disable iff (!Rst)
    (Rx_flag) |-> ##2 Rx_FlagDetect; 
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

  //10. Abort pattern detected during valid frame should generate Rx AbortSignal.
  property RX_AbortSignalWhenValid;
    @(posedge Clk) disable iff (!Rst)
    ##1 (Rx_AbortDetect && Rx_ValidFrame) |=> Rx_AbortSignal;
  endproperty

  RX_AbortSignalWhenValid_Assert : assert property (RX_AbortSignalWhenValid) begin
    $display("PASS. AbortSignal was generated when abort pattern was detected");
  end else begin 
    $error("AbortSignal did not go high after AbortDetect during validframe"); 
    ErrCntAssertions++; 
  end

  //13. When receiving more than 128 bytes, Rx Overflow should be asserted.
  property RX_Overflow_Detect;
    @(posedge Clk) disable iff (!Rst || !Rx_ValidFrame)
    $rose(Rx_ValidFrame) ##0 ($rose(Rx_NewByte) [->129]) |=> $rose(Rx_Overflow)
  endproperty

  RX_Overflow_Assert : assert property (RX_Overflow_Detect) begin
    $display("PASS: RX_Overflow detected afrer more than 128 bytes received");
  end else begin
    $error("RX_Overflow did not go high after receiving more than 128 bytes");
    ErrCntAssertions++;
  end

  // 14
  logic [7:0] byte_counter; // Counter to track the number of bytes received
  // Update the byte counter
  always_ff @(posedge Clk or negedge Rst) begin
    if (!Rst) begin
      byte_counter <= 8'd0;
    end else if ($fell(Rx_EoF)) begin
      byte_counter <= 8'd0; // Reset the counter when not in a valid frame
    end else if ($rose(Rx_NewByte)) begin
      byte_counter <= byte_counter + 1; // Increment the counter on each new byte
      $display("byte_counter %0d", byte_counter);
    end
  end

  // 14. Rx_FrameSize should equal the exact number of bytes received in a frame (max. 126 bytes).
  property RX_FrameSize_Exact;
    @(posedge Clk) disable iff (!Rst)
    ($rose(Rx_EoF) and !Rx_FrameError and !Rx_Overflow) |-> ##1 (Rx_FrameSize == (byte_counter-2));
  endproperty

  RX_FrameSize_Exact_Assert : assert property (RX_FrameSize_Exact) begin
    $display("PASS: Rx_FrameSize matches the exact number of bytes received.");
  end else begin
    $error("FAIL: Rx_FrameSize does not match the exact number of bytes received. Expected: %0d, Got: %0d", byte_counter-2, Rx_FrameSize);
    ErrCntAssertions++;
  end
  property RX_FrameSize_Exact;
    @(posedge Clk) disable iff (!Rst)
    ($rose(Rx_EoF) and !Rx_FrameError and !Rx_Overflow) |-> ##1 (Rx_FrameSize == (byte_counter-2));
  endproperty

  RX_FrameSize_Exact_Assert : assert property (RX_FrameSize_Exact) begin
    $display("PASS: Rx_FrameSize matches the exact number of bytes received.");
  end else begin
    $error("FAIL: Rx_FrameSize does not match the exact number of bytes received. Expected: %0d, Got: %0d", byte_counter-2, Rx_FrameSize);
    ErrCntAssertions++;
  end

  //15. Rx Ready should indicate byte(s) in RX buffer is(are) ready to be read.
  property RX_Ready;
    @(posedge Clk) disable iff (!Rst)
    (!Rx_Ready ##1 Rx_Ready) |-> (Rx_EoF); //Whole RX frame has been received, end of frame
  endproperty

  RX_Ready_Assert : assert property(RX_Ready) begin
    $display("PASS: Bytes in RX Buffer are ready to be read");
  end else begin
    $error("FAIL: EoF is not asserted when buffer is ready");
    ErrCntAssertions++;
  end

  //16. Non-byte aligned data or error in FCS checking should result in frame error.
  property FCSerrFrameerr;
    @(posedge Clk) disable iff (!Rst)
    !Rx_FCSerr ##1 Rx_FCSerr && Rx_FCSen |=> Rx_FrameError;
  endproperty

  FCSerrFrameerr_Assert : assert property(FCSerrFrameerr) begin
    $display("PASS. Non-byte aligned data or error in FCS checking resulted in frame error");
  end else begin
    $error("FAIL. FCSerrFrameerr_Assertion does not work");
    ErrCntAssertions++;
  end

  //17. Tx Done should be asserted when the entire TX buffer has been read for transmission (IMMEDIATE)
  property TX_Done;
    @(posedge Clk) disable iff (!Rst)
    Tx_DataAvail ##1 !Tx_DataAvail |-> Tx_Done;
  endproperty

  TX_Done_Assert : assert property(TX_Done) begin
    $display("PASS: Imm. Tx_done asserted after no data available");
  end else begin
    $error("FAIL: Imm Tx_done not asserted properly after no data available");
    ErrCntAssertions++;
  end

endmodule
