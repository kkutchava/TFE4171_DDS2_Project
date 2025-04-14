//////////////////////////////////////////////////
// Title:   testPr_hdlc
// Author: 
// Date:  
//////////////////////////////////////////////////

/* testPr_hdlc contains the simulation and immediate assertion code of the
   testbench. 

   For this exercise you will write immediate assertions for the Rx module which
   should verify correct values in some of the Rx registers for:
   - Normal behavior
   - Buffer overflow 
   - Aborts

   HINT:
   - A ReadAddress() task is provided, and addresses are documentet in the 
     HDLC Module Design Description
*/

program testPr_hdlc(
  in_hdlc uin_hdlc
);
  
  int TbErrorCnt;

  /****************************************************************************
   *                                                                          *
   *                               Student code                               *
   *                                                                          *
   ****************************************************************************/
  // Define bit masks for each field
  localparam logic [7:0] MASK_RX_ABORT = 8'b0000_1000;
  const string MESSAGE_RX_ABORT = "RX Status/Control received abort sequence";
  
  localparam logic [7:0] MASK_RX_NORMAL  = 8'b0000_0001;
  const string MESSAGE_RX_NORMAL = "RX Status/Control received normal sequence";

  localparam logic [7:0] MASK_RX_OVERFLOW    = 8'b0001_0001;
  const string MESSAGE_RX_OVERFLOW = "RX Status/Control received overflow sequence";

  //3. Correct bits set in RX status/control register after receiving frame. 
  //Remember to check all bits. I.e. after an abort the Rx Overflow bit should be 0, unless an overflow also occurred.

  // VerifyAbortReceive should verify correct value in the Rx status/control
  // register, and that the Rx data buffer is zero after abort.
  task VerifyAbortReceive(logic [127:0][7:0] data, int Size);
    logic [7:0] ReadData;

    // Read the RX status/control register at address 0x2
    ReadAddress(3'h2, ReadData);

    // Assert the mask in the RX status/control register
    assert ((ReadData & MASK_RX_ABORT) != 0)
      $display("PASS: %s", MESSAGE_RX_ABORT);
      else $error("FAIL: %s, Got %b", MESSAGE_RX_ABORT, ReadData);

    // INSERT CODE HERE
        /*
    assert (!uin_hdlc.Rx_Ready)
      $display("PASS: Rx_Ready: LOW\n");
      else $error("failed Rx_Ready");
    assert (uin_hdlc.Rx_AbortSignal)
      $display("PASS: Rx_AbortSignal: HIGH\n");
      else $error("failed Rx_AbortSignal");
    assert (!uin_hdlc.Rx_Overflow)
      $display("PASS: Rx_Overflow: HIGH\n");
      else $error("failed Rx_Overflow");
    assert (!uin_hdlc.Rx_FrameError)
      $display("PASS: Rx_FrameError: LOW\n");
      else $error("failed Rx_FrameError");*/
    
    ReadAddress(3'h3, ReadData);
      assert (ReadData === 8'h00)
        $display("PASS. Rx_Buff has correct data");
        else $error("Rx data buffer is not zero after abort: Got %h", ReadData);

  endtask

  // VerifyNormalReceive should verify correct value in the Rx status/control
  // register, and that the Rx data buffer contains correct data.
  task VerifyNormalReceive(logic [127:0][7:0] data, int Size);
    logic [7:0] ReadData;
    wait(uin_hdlc.Rx_Ready);

    // Read the RX status/control register at address 0x2
    ReadAddress(3'h2, ReadData);

    // Assert the mask in the RX status/control register
    assert ((ReadData & MASK_RX_NORMAL) != 0)
      $display("PASS: %s", MESSAGE_RX_NORMAL);
      else $error("FAIL: %s, Got %b", MESSAGE_RX_NORMAL, ReadData);

    // INSERT CODE HERE
    /*
    assert (uin_hdlc.Rx_Ready && !uin_hdlc.Rx_Overflow && !uin_hdlc.Rx_FrameError && !uin_hdlc.Rx_AbortSignal)
      else $error("failed VerifyNormalReceive");*/
      
    // Loop through "Size" and compare "data" with "ReadData"
    for (int i = 0; i < Size; i++) begin
      wait(uin_hdlc.Rx_Ready); //Check if needed 
      ReadAddress(3'h3, ReadData);
      assert (ReadData === data[i])
        $display("PASS. Rx_Buff has correct data");
        else $error("Data mismatch at index %0d: Expected %h, Got %h", i, data[i], ReadData);
    end

  endtask

  // VerifyNormalReceive should verify correct value in the Rx status/control
  // register, and that the Rx data buffer contains correct data.
  task VerifyOverflowReceive(logic [127:0][7:0] data, int Size);
    logic [7:0] ReadData;
    wait(uin_hdlc.Rx_Ready);

    // Read the RX status/control register at address 0x2
    ReadAddress(3'h2, ReadData);

    // Assert the mask in the RX status/control register
    assert ((ReadData & MASK_RX_OVERFLOW) != 0)
      $display("PASS: %s", MESSAGE_RX_OVERFLOW);
      else $error("FAIL: %s, Got %b", MESSAGE_RX_OVERFLOW, ReadData);

    // INSERT CODE HERE
    /*
    assert (uin_hdlc.Rx_Ready && uin_hdlc.Rx_Overflow && !uin_hdlc.Rx_FrameError && !uin_hdlc.Rx_AbortSignal)
      else $error("failed VerifyOverflowReceive");*/
    
    // Loop through "Size" and compare "data" with "ReadData"
    for (int i = 0; i < Size; i++) begin
      wait(uin_hdlc.Rx_Ready); //Check if needed 
      ReadAddress(3'h3, ReadData);
      assert (ReadData === data[i])
        $display("PASS. Rx_Buff has correct data");
        else $error("Data mismatch at index %0d: Expected %h, Got %h", i, data[i], ReadData);
    end
  
  endtask



  

  /****************************************************************************
   *                                                                          *
   *                             Simulation code                              *
   *                                                                          *
   ****************************************************************************/

  typedef enum {
    ADDR_TX_CS   = 0,
    ADDR_TX_BUFF = 1
  } hdlc_reg_addrs_e;
  
  typedef struct packed{
    bit [7:5] reserved;
    bit full;
    bit abortedTrans;
    bit abortFrame;
    bit enable;
    bit done;
  } reg_tx_sc_t;

  reg_tx_sc_t reg_tx_sc;

  byte my_data_q[$];
  byte my_curr;
  shortint my_fcs;
  byte unsigned my_curr_size;
  const byte STARTEND_FLAG = 8'h7E;
  const byte ABORT_FLAG = 8'hFE;
  //const byte my_flag = 8'hBF;
  byte removed_a_zero;

  enum {
    WAITING_FOR_FLAG,
    RECEIVING
  } state;

  initial begin
    state = WAITING_FOR_FLAG;
    my_curr = '1;
    my_curr_size = 0;
    removed_a_zero = 0;
  end

  initial forever begin
    @(negedge uin_hdlc.Clk)
    if (uin_hdlc.WriteEnable && uin_hdlc.Address == ADDR_TX_CS) begin
      reg_tx_sc = uin_hdlc.DataIn[7:0];
      if (reg_tx_sc.enable) begin
        automatic logic [127:0] [7:0] data = 0;
        foreach (my_data_q[idx]) begin
          data[idx] = my_data_q[idx];
        end
        GenerateFCSBytes(data, my_data_q.size(), my_fcs);
        $display("%t: Register Monitor: Detected start of TX transmission. Expecting FCS: 0x%04x", $time, my_fcs);
      end
    end
    if (uin_hdlc.WriteEnable && uin_hdlc.Address == ADDR_TX_BUFF) begin
      my_data_q.push_back(uin_hdlc.DataIn[7:0]);
      $display("%t: Register Monitor: Pushed 0x%02x to data queue", $time, uin_hdlc.DataIn[7:0]);
    end
  end

  initial forever begin
    @(posedge uin_hdlc.Clk);
    #0;
    my_curr >>= 1;
    my_curr[7] |= uin_hdlc.Tx;
    if (my_curr_size < 8) my_curr_size ++;
    //if (my_curr != 8'hff) $display("%t: TX Monitor: Current 0x%02x (size: %0d) (removed a zero: %0d) (Tx: %0d) ", $time, my_curr, my_curr_size, removed_a_zero, uin_hdlc.Tx);
    if (state == WAITING_FOR_FLAG) begin
      if (my_curr == STARTEND_FLAG) begin
        ass_start_flag: assert(1);
        state = RECEIVING;
       // $display("%t: TX Monitor: Going to state %s", $time, state.name());
        my_curr_size = 0;
        my_curr = 0;
      end else if (my_curr_size == 8) begin
        // Assumes we can have one zero in buffer in case of the start flag
        ass_idle: assert($countones(my_curr) >= 7) else $fatal(); 
      end
    end else if (state == RECEIVING) begin/*
      if (!removed_a_zero && my_curr == ABORT_FLAG) begin
        $display("Reveiving flag 0x%02x tryitng to assert frame", my_curr); 
        assert_abort_flag: assert(uin_hdlc.Tx_AbortedTrans == 1) $display("ABORT FLAG IS ASSERTED CORRECTLY"); 
          else $error("%t: TX Monitor: Current 0x%02x (size: %0d) (removed a zero: %0d) (Tx: %0d) ", $time, my_curr, my_curr_size, removed_a_zero, uin_hdlc.Tx);
        state = WAITING_FOR_FLAG;
        my_curr_size = 0;
        $display("%t: TX Monitor: Going to state %s", $time, state.name());
      end 
      else*/ if (!removed_a_zero && my_curr == STARTEND_FLAG) begin
        ass_end_flag: assert(1);
        state = WAITING_FOR_FLAG;
        my_curr_size = 0;
      //  $display("%t: TX Monitor: Going to state %s", $time, state.name());
      end else begin
        if (!removed_a_zero && my_curr ==? 8'b011111xx) begin
          //$display("%t: TX Monitor: Removing a zero", $time);
          my_curr_size--;
          my_curr <<= 1;
          removed_a_zero = 5;
        end else begin
          removed_a_zero = removed_a_zero ? removed_a_zero-1 : 0;
        end
        if (my_curr_size == 8) begin  
          //$display("%t: TX Monitor: Received byte 0x%02x.", $time, my_curr);
          // When out of bytes in the queue expect to receive the FCS
          if (my_data_q.size() == 0 && reg_tx_sc.enable) begin
            ass_tx_fcs: assert (my_curr == my_fcs[7:0])
            else $error("%t: TX Monitor: Expecting 0x%02x instead of 0x%02x (FCS)", $time, my_fcs[7:0], my_curr);
            my_fcs >>= 8;
          end else begin
            automatic byte expected_shit = my_data_q.pop_front();
            ass_rx_data: assert (my_curr == expected_shit)
            else $error("%t: TX Monitor: Expecting 0x%02x instead of 0x%02x", $time, expected_shit, my_curr);
          end
          my_curr_size = 0;
        end
      end
    end
  end

  initial begin
    $display("*************************************************************");
    $display("%t - Starting Test Program", $time);
    $display("*************************************************************");

    Init();

    //Receive: Size, Abort, FCSerr, NonByteAligned, Overflow, Drop, SkipRead
    Receive( 10, 0, 0, 0, 0, 0, 0); //Normal
    Receive( 40, 1, 0, 0, 0, 0, 0); //Abort
    Receive(126, 0, 0, 0, 1, 0, 0); //Overflow
    Receive( 45, 0, 0, 0, 0, 0, 0); //Normal
    Receive(126, 0, 0, 0, 0, 0, 0); //Normal
    Receive(122, 1, 0, 0, 0, 0, 0); //Abort
    Receive(126, 0, 0, 0, 1, 0, 0); //Overflow
    Receive( 25, 0, 0, 0, 0, 0, 0); //Normal
    Receive( 47, 0, 0, 0, 0, 0, 0); //Normal

    repeat (1) begin
      SendRandomShit(0);
      //SendRandomShit(1);
      #1ms;
      //SendRandomShit(2);
      #1ms;
      SendRandomShit(3);
      #1ms;
      SendRandomShit(4);
      SendRandomShit(8);
      SendRandomShit(16);
      SendRandomShit(32);
      SendRandomShit(32);
      SendRandomShit(64);
      SendRandomShit(64);
      SendRandomShit(126);

      
    end

    $display("*************************************************************");
    $display("%t - Finishing Test Program", $time);
    $display("*************************************************************");
    $stop;
  end

  final begin

    $display("*********************************");
    $display("*                               *");
    $display("* \tAssertion Errors: %0d\t  *", TbErrorCnt + uin_hdlc.ErrCntAssertions);
    $display("*                               *");
    $display("*********************************");

  end

  task Init();
    uin_hdlc.Clk         =   1'b0;
    uin_hdlc.Rst         =   1'b0;
    uin_hdlc.Address     = 3'b000;
    uin_hdlc.WriteEnable =   1'b0;
    uin_hdlc.ReadEnable  =   1'b0;
    uin_hdlc.DataIn      =     '0;
    uin_hdlc.TxEN        =   1'b1;
    uin_hdlc.Rx          =   1'b1;
    uin_hdlc.RxEN        =   1'b1;

    TbErrorCnt = 0;

    #1000ns;
    uin_hdlc.Rst         =   1'b1;
  endtask

  task WriteAddress(input logic [2:0] Address ,input logic [7:0] Data);
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Address     = Address;
    uin_hdlc.WriteEnable = 1'b1;
    uin_hdlc.DataIn      = Data;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.WriteEnable = 1'b0;
  endtask

  task ReadAddress(input logic [2:0] Address ,output logic [7:0] Data);
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Address    = Address;
    uin_hdlc.ReadEnable = 1'b1;
    #100ns;
    Data                = uin_hdlc.DataOut;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.ReadEnable = 1'b0;
  endtask

  task InsertFlagOrAbort(int flag);
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b0;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    if(flag)
      uin_hdlc.Rx = 1'b0; //end
    else
      uin_hdlc.Rx = 1'b1; //abort
  endtask

  task MakeRxStimulus(logic [127:0][7:0] Data, int Size);
    logic [4:0] PrevData;
    PrevData = '0;
    for (int i = 0; i < Size; i++) begin
      for (int j = 0; j < 8; j++) begin
        if(&PrevData) begin
          @(posedge uin_hdlc.Clk);
          uin_hdlc.Rx = 1'b0;
          PrevData = PrevData >> 1;
          PrevData[4] = 1'b0;
        end

        @(posedge uin_hdlc.Clk);
        uin_hdlc.Rx = Data[i][j];

        PrevData = PrevData >> 1;
        PrevData[4] = Data[i][j];
      end
    end
  endtask

  // Write Tx_Enable in Tx_SC
  // If still more to send wait for Tx_Done
  // 
  // What happpens when writing to Tx buffer after enable before it has its content
  // What happpens when using 0 size buffer
  task SendRandomShit(shortint num_bytes);
  logic  [7:0] ReadData;
    reg_tx_sc_t tx_statusControl;
    automatic byte num_bytes_sent_to_tx_buffer = 0;
    //byte bytes_pushed_to_buffer[$];
    
    $display("%t: SendRandomShit(%0d)", $time, num_bytes);

    // What are we even doing here?
    if (!(num_bytes inside {[1:128]})) begin
      $display("%t: Cannot send more bytes that what Tx Buffer can hold!", $time);
      return;
    end

    // Clearing Status and Control register
    tx_statusControl = '0;
    WriteAddress(0, tx_statusControl);

    // Push to buffer util Tx_Full unless all is in
    
    //$display("%t: TX transmission: Filling Tx Buffer", $time);
    while (!tx_statusControl.full && num_bytes_sent_to_tx_buffer < num_bytes) begin
      byte to_push_to_buffer;
      to_push_to_buffer = $urandom;
      WriteAddress(1, to_push_to_buffer);
      num_bytes_sent_to_tx_buffer++;
      //bytes_pushed_to_buffer.push_back(to_push_to_buffer);
      ReadAddress(0, tx_statusControl);
    end

    // Start sending by writing to enable in Tx_CS register
    tx_statusControl.enable = 1;
    WriteAddress(0, tx_statusControl);
    //$display("%t: TX transmission: Started", $time);

    // Wait until all has been sent
    //do begin
    //  ReadAddress(0, tx_statusControl);
    //end while(!tx_statusControl.done);

/*
    repeat(num_bytes/2) @(posedge uin_hdlc.Clk); //abort in the middle
    $display("%t: TX transmission: Sending abort after %0d number of cycles", $time, num_bytes/2);
    
    // Send the abort signal
    tx_statusControl = '0;
    tx_statusControl.abortFrame = 1;
    tx_statusControl.enable = 0;
    WriteAddress(0, tx_statusControl);
    @(posedge uin_hdlc.Clk);
    @(posedge uin_hdlc.Clk);
    
    ReadAddress(3'b000, ReadData);
    ReadData = ReadData & 8'b1111_1001;
    assert (ReadData == (8'b0000_1000 | 8'b0000_0001)) begin
        $display("PASS: Verifying Tx_AbortedTrans in control register is correct");
    end else begin
        $error("FAIL: Expected Tx_sc = 0x09, Received Tx_sc = 0x%h", ReadData);
    end
    @(posedge uin_hdlc.Clk);
    @(posedge uin_hdlc.Clk);
    repeat(10) begin
        @(posedge uin_hdlc.Clk);
            assert (uin_hdlc.Tx == 1'b1) else begin
                $error("FAIL: in idle now Expected Tx = 0b1");
            end
    end

*/
    wait(uin_hdlc.Tx_Done);
    $display("%t: TX transmission: TX Buffer Done", $time);

    wait(state == WAITING_FOR_FLAG);
    $display("%t: TX transmission: Done (flag detected)", $time);
    #5us;
  endtask

        //   logic  [7:0] ReadData;
        // WriteAddress(3'b000, 8'b0000_0100);
        // $display("checking Tx_AbortedTrans flag should be 1 while it is %b", uin_hdlc.Tx_AbortedTrans);
        // @(posedge uin_hdlc.Clk);
        // $display("checking Tx_AbortedTrans flag should be 1 while it is %b", uin_hdlc.Tx_AbortedTrans);
        // @(posedge uin_hdlc.Clk);
        // $display("checking Tx_AbortedTrans flag should be 1 while it is %b", uin_hdlc.Tx_AbortedTrans);
        // ReadAddress(3'b000, ReadData);
        // ReadData = ReadData & 8'b1111_1001;
        // assert (ReadData == (8'b0000_1000 | 8'b0000_0001)) begin
        //     $display("PASS: VerifyAbortTransmit:: Tx_SC correct");
        // end else begin
        //     $error("FAIL: VerifyAbortTransmit:: Expected Tx_SC = 0x09, Received Tx_SC = 0x%h", ReadData);
        // end
        // @(posedge uin_hdlc.Clk);
        // @(posedge uin_hdlc.Clk);
        // repeat(10) begin
        //     @(posedge uin_hdlc.Clk);
        //         assert (uin_hdlc.Tx == 1'b1) else begin
        //             $error("FAIL: VerifyAbortTransmit:: Expected Tx = 0b1");
        //             TbErrorCnt++;
        //         end
        // end
       

  task Receive(int Size, int Abort, int FCSerr, int NonByteAligned, int Overflow, int Drop, int SkipRead);
    logic [127:0][7:0] ReceiveData;
    logic       [15:0] FCSBytes;
    logic   [2:0][7:0] OverflowData;
    string msg;
    if(Abort)
      msg = "- Abort";
    else if(FCSerr)
      msg = "- FCS error";
    else if(NonByteAligned)
      msg = "- Non-byte aligned";
    else if(Overflow)
      msg = "- Overflow";
    else if(Drop)
      msg = "- Drop";
    else if(SkipRead)
      msg = "- Skip read";
    else
      msg = "- Normal";
    $display("*************************************************************");
    $display("%t - Starting task Receive %s", $time, msg);
    $display("*************************************************************");

    for (int i = 0; i < Size; i++) begin
      ReceiveData[i] = $urandom;
    end
    ReceiveData[Size]   = '0;
    ReceiveData[Size+1] = '0;

    //Calculate FCS bits;
    GenerateFCSBytes(ReceiveData, Size, FCSBytes);
    ReceiveData[Size]   = FCSBytes[7:0];
    ReceiveData[Size+1] = FCSBytes[15:8];

    //Enable FCS
    if(!Overflow && !NonByteAligned)
      WriteAddress(8'h2, 8'h20);
    else
      WriteAddress(8'h2, 8'h00);

    //Generate stimulus
    InsertFlagOrAbort(1);
    
    MakeRxStimulus(ReceiveData, Size + 2);
    
    if(Overflow) begin
      OverflowData[0] = 8'h44;
      OverflowData[1] = 8'hBB;
      OverflowData[2] = 8'hCC;
      MakeRxStimulus(OverflowData, 3);
    end

    if(Abort) begin
      InsertFlagOrAbort(0);
    end else begin
      InsertFlagOrAbort(1);
    end

    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;

    repeat(8)
      @(posedge uin_hdlc.Clk);

    //VerifyCorrectDatainRX(Size);
    
    if(Abort) begin
      VerifyAbortReceive(ReceiveData, Size);
    end else if(Overflow) begin
      VerifyOverflowReceive(ReceiveData, Size);
    end else if(!SkipRead) begin
      VerifyNormalReceive(ReceiveData, Size);
    end

    #5000ns;
  endtask

  function void GenerateFCSBytes(logic [127:0][7:0] data, int size, output logic[15:0] FCSBytes);
    logic [23:0] CheckReg;
    CheckReg[15:8]  = data[1];
    CheckReg[7:0]   = data[0];
    for(int i = 2; i < size+2; i++) begin
      CheckReg[23:16] = data[i];
      for(int j = 0; j < 8; j++) begin
        if(CheckReg[0]) begin
          CheckReg[0]    = CheckReg[0] ^ 1;
          CheckReg[1]    = CheckReg[1] ^ 1;
          CheckReg[13:2] = CheckReg[13:2];
          CheckReg[14]   = CheckReg[14] ^ 1;
          CheckReg[15]   = CheckReg[15];
          CheckReg[16]   = CheckReg[16] ^1;
        end
        CheckReg = CheckReg >> 1;
      end
    end
    FCSBytes = CheckReg;
    $display("%t: GenerateFCSBytes(0x%0x, %0d, 0x%04x)", $time, data, size, FCSBytes);
  endfunction

endprogram
