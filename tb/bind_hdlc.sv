//////////////////////////////////////////////////
// Title:   bind_hdlc
// Author:  Karianne Krokan Kragseth
// Date:    20.10.2017
//////////////////////////////////////////////////

module bind_hdlc ();

  bind test_hdlc assertions_hdlc u_assertion_bind(
    .ErrCntAssertions (uin_hdlc.ErrCntAssertions),
    .Clk              (uin_hdlc.Clk),
    .Rst              (uin_hdlc.Rst),
    .Rx               (uin_hdlc.Rx),
    .Rx_FlagDetect    (uin_hdlc.Rx_FlagDetect),
    .Rx_ValidFrame    (uin_hdlc.Rx_ValidFrame),
    .Rx_AbortDetect   (uin_hdlc.Rx_AbortDetect),
    .Rx_AbortSignal   (uin_hdlc.Rx_AbortSignal),
    .Rx_Overflow      (uin_hdlc.Rx_Overflow),
    .Rx_WrBuff        (uin_hdlc.Rx_WrBuff),
    .Rx_EoF           (uin_hdlc.Rx_EoF),
    .Rx_Ready         (uin_hdlc.Rx_Ready),
    .Rx_FCSerr        (uin_hdlc.Rx_FCSerr),
    .Rx_FCSen         (uin_hdlc.Rx_FCSen),
    .Rx_FrameError    (uin_hdlc.Rx_FrameError),
    .Tx_DataAvail     (uin_hdlc.Tx_DataAvail),
    .Tx_Done          (uin_hdlc.Tx_Done),
    .Rx_NewByte       (uin_hdlc.Rx_NewByte),
    .Rx_FrameSize     (uin_hdlc.Rx_FrameSize)
  );

endmodule
