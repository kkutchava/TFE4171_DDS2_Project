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
  input  logic Tx_Done
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
