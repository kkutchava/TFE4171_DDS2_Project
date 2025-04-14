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

  // VerifyAbortReceive should verify correct value in the Rx status/control
  // register, and that the Rx data buffer is zero after abort.
  task VerifyAbortReceive(logic [127:0][7:0] data, int Size);
    logic [7:0] ReadData;

    // INSERT CODE HERE
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
      else $error("failed Rx_FrameError");
    
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

    // INSERT CODE HERE
    assert (uin_hdlc.Rx_Ready && !uin_hdlc.Rx_Overflow && !uin_hdlc.Rx_FrameError && !uin_hdlc.Rx_AbortSignal)
      else $error("failed VerifyNormalReceive");
      
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

    // INSERT CODE HERE
    assert (uin_hdlc.Rx_Ready && uin_hdlc.Rx_Overflow && !uin_hdlc.Rx_FrameError && !uin_hdlc.Rx_AbortSignal)
      else $error("failed VerifyOverflowReceive");
    
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
    if (my_curr != 8'hff) $display("%t: TX Monitor: Current 0x%02x (size: %0d) (removed a zero: %0d) (Tx: %0d) ", $time, my_curr, my_curr_size, removed_a_zero, uin_hdlc.Tx);
    if (state == WAITING_FOR_FLAG) begin
      //$display("INSIDE THE WAITING_FOR_FLAG");
      if (my_curr == STARTEND_FLAG) begin
        ass_start_flag: assert(1); //5. starts of frame beh
        state = RECEIVING;
        $display("%t: TX Monitor: Going to state %s", $time, state.name());
        my_curr_size = 0;
        my_curr = 0;
      end else if (my_curr_size == 8) begin
        // Assumes we can have one zero in buffer in case of the start flag
        //7. Idle pattern generation and checking (1111 1111 when not operating).
        ass_idle: assert($countones(my_curr) >= 7) else $fatal(); 
      end
    end else if (state == RECEIVING) begin
      if (!removed_a_zero && my_curr == ABORT_FLAG) begin // ABORT BEHAVIOR
        //8. Abort pattern generation and checking (1111 1110). Remember that the 0 must be sent first
        assert(1) $display("PASS: Abort pattern 0x%02x received after abort set in TX_SC reg", my_curr); 
          else $error("FAIL. Expected 0xfe while received %x", my_curr); //roughly impossible if we are in this IF-statemnt
        //9. When aborting frame during transmission, Tx AbortedTrans should be asserted.
        assert_abort_flag: assert(uin_hdlc.Tx_AbortedTrans == 1) $display("PASS: Tx AbortedTrans is set correctly after abort"); 
          else $error("%t: TX Monitor: Current 0x%02x (size: %0d) (removed a zero: %0d) (Tx: %0d) ", $time, my_curr, my_curr_size, removed_a_zero, uin_hdlc.Tx);
        state = WAITING_FOR_FLAG;
        my_curr_size = 0;
        $display("%t: TX Monitor: Going to state %s", $time, state.name());
      end else if (!removed_a_zero && my_curr == STARTEND_FLAG) begin
        ass_end_flag: assert(1); //5. END OF FRAME BEHAVIOR
        state = WAITING_FOR_FLAG;
        my_curr_size = 0;
        //17. Tx Done should be asserted when the entire TX buffer has been read for transmission.
        assert_tx_done : assert(uin_hdlc.Tx_Done) begin
          $display("PASS. Tx_done asserted after tranmission is done");
        end else begin
          $error("FAIL. Tx_done is not asserted after transmission or idk");
          //ErrCntAssertions++;
        end
        $display("%t: TX Monitor: Going from ENDFRAME to state %s", $time, state.name());
      end else begin //NORMAL FLOW
        if (!removed_a_zero && my_curr ==? 8'b011111xx) begin
          //$display("%t: TX Monitor: Removing a zero", $time);
          my_curr_size--;
          my_curr <<= 1;
          removed_a_zero = 5;
        end else begin
          removed_a_zero = removed_a_zero ? removed_a_zero-1 : 0;
        end
        if (my_curr_size == 8 && !uin_hdlc.Tx_AbortedTrans) begin  
          //$display("%t: TX Monitor: Received byte 0x%02x.", $time, my_curr);
          // When out of bytes in the queue expect to receive the FCS
          if (my_data_q.size() == 0 && reg_tx_sc.enable) begin
            //11. CRC generation and Checking.
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
    
    $display("%t: TX transmission: Filling Tx Buffer", $time);
    while (!tx_statusControl.full && num_bytes_sent_to_tx_buffer < num_bytes) begin
      byte to_push_to_buffer;
      to_push_to_buffer = $urandom;
      WriteAddress(1, to_push_to_buffer);
      num_bytes_sent_to_tx_buffer++;
      //bytes_pushed_to_buffer.push_back(to_push_to_buffer);
      ReadAddress(0, tx_statusControl);
    end
    //18. Tx Full should be asserted after writing 126 or more bytes to the TX buffer (overflow).
    if (num_bytes_sent_to_tx_buffer >= 126) begin
      ReadAddress(0, tx_statusControl);
      tx_full_assert : assert(tx_statusControl.full) begin
        $display("PASS. TX Full asserted after receiving more or 126 bytes");
      end else begin
        $error("FAIL. num_bytes_sent_to_tx_buffer is %0d Tx full in SC reg is %0d", num_bytes_sent_to_tx_buffer, tx_statusControl.full);
      end
    end

    // Start sending by writing to enable in Tx_CS register
    tx_statusControl.enable = 1;
    WriteAddress(0, tx_statusControl);
    $display("%t: TX transmission: Started", $time);

    wait(uin_hdlc.Tx_Done);
    $display("%t: TX transmission: TX Buffer Done", $time);

    wait(state == WAITING_FOR_FLAG);
    $display("%t: TX transmission: Done (flag detected)", $time);
    #5us;
  endtask

int abort_count = 0;
  initial forever begin //SENDING ABORT
  @(posedge uin_hdlc.Clk);
  #0;
    if (abort_count < 3 && //limit number of aborts
        $urandom_range(0, 99) < 2 && // ~2% probability
        state == RECEIVING &&
        !(!removed_a_zero && my_curr == ABORT_FLAG) &&
        !(!removed_a_zero && my_curr == STARTEND_FLAG)
    ) begin //NORMAL FLOW
      logic  [7:0] ReadData;
      reg_tx_sc_t tx_statusControl;
      abort_count++;
      repeat(16) @(posedge uin_hdlc.Clk); //wait for half of the frame
      //repeat(num_bytes/2) @(posedge uin_hdlc.Clk); //abort in the middle
      $display("%0t: TX transmission: Sending abort after %0d number of cycles", $time, 16);
      // Send the abort signal
      tx_statusControl = '0;
      tx_statusControl.abortFrame = 1;
      tx_statusControl.enable = 0; 
      WriteAddress(0, tx_statusControl);
      @(posedge uin_hdlc.Clk);
      @(posedge uin_hdlc.Clk);
      
      ReadAddress(3'b000, ReadData);
      my_data_q = {}; //empty the queue
      ReadData = ReadData & 8'b1111_1001;
      $display("read data from the tx_statusControl is %x", ReadData);
      // asserts that TX status control register is set correctly
      assert (ReadData == 8'b0000_1001) begin
          $display("PASS: AbortedTrans in TX_SC (status control) register is correct");
      end else begin
          $error("FAIL: Expected Tx_sc = 0x09, Received Tx_sc = 0x%h", ReadData);
      end
      repeat(12) @(posedge uin_hdlc.Clk); // should reach other modules too not sure
      //@(posedge uin_hdlc.Clk);
      // repeat(10) begin
      //     @(posedge uin_hdlc.Clk);
      //         assert (uin_hdlc.Tx == 1'b1) else begin
      //             $error("FAIL: in idle now Expected Tx = 0b1");
      //         end
      // end
    end

  end

  task Receive(int Size, int Abort, int FCSerr, int NonByteAligned, int Overflow, int Drop, int SkipRead);
    logic [127:0][7:0] ReceiveData;
    logic       [15:0] FCSBytes;
    logic   [2:0][7:0] OverflowData;
    logic [7:0] rx_status_reg;
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
    
    if(Abort) begin
      VerifyAbortReceive(ReceiveData, Size);
      // ReadAddress(2, rx_status_reg);
      // $display("ABORT: RX STATUS REG contetnt %b", rx_status_reg);
    end
    else if(Overflow) begin
      VerifyOverflowReceive(ReceiveData, Size);
      //wait(uin_hdlc.Rx_Ready);
      // ReadAddress(2, rx_status_reg);
      // $display("OVERFLOW: RX STATUS REG contetnt %b", rx_status_reg);
    end
    else if(!SkipRead) begin
      VerifyNormalReceive(ReceiveData, Size);
      //wait(uin_hdlc.Rx_Ready);
      // ReadAddress(2, rx_status_reg);
      // $display("NORMAL: RX STATUS REG contetnt %b", rx_status_reg);
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

  covergroup cg @ (posedge uin_hdlc.Clk);
        //OUTER SIGNALS:
        //Address:
  	    Address : coverpoint uin_hdlc.Address {
            bins tx_sc = {0};
            bins tx_buff = {1};
            bins rx_sc = {2};
            bins rx_buff = {3};
            bins rx_len = {4};
            ignore_bins invalid = {[5:7]};
	      }
        WriteEnable : coverpoint uin_hdlc.WriteEnable {
          bins wne = {0};
          bins we = {1};
        }
        ReadEnable : coverpoint uin_hdlc.ReadEnable {
          bins rne = {0};
          bins re = {1};
        }
        DataIn : coverpoint uin_hdlc.DataIn {
          bins datain[] = {[0:127]};
        }
        DataOut : coverpoint uin_hdlc.DataOut {
          bins dataout[] = {[0:127]};
        }
        // TX
        Tx : coverpoint uin_hdlc.Tx {
          bins txz = {0};
          bins tx1 = {1};
        }
        TxEN : coverpoint uin_hdlc.TxEN {
          bins txnen = {0};
          bins txen = {1};
        }
        Tx_Done : coverpoint uin_hdlc.Tx_Done {
          bins ndone = {0};
          bins done = {1};
        }
        // RX
        Rx  : coverpoint uin_hdlc.Rx {
          bins rxz = {0};
          bins rx1 = {1};
        }
        RxEN : coverpoint uin_hdlc.RxEN {
          bins rxnen = {0};
          bins rxen = {1};
        }
        Rx_Ready : coverpoint uin_hdlc.Rx_Ready {
          bins nready = {0};
          bins ready = {1};
        }

        //INNER SIGNALS:
        //RX
        Rx_ValidFrame : coverpoint uin_hdlc.Rx_ValidFrame { 
          bins valid = {1}; 
          bins invalid = {0}; 
        }
        Rx_Data : coverpoint uin_hdlc.Rx_Data { 
          bins data[] = {[7:0]}; 
        }
        Rx_AbortSignal : coverpoint uin_hdlc.Rx_AbortSignal { 
          bins abort = {1}; 
          bins no_abort = {0}; 
        }
        Rx_WrBuff : coverpoint uin_hdlc.Rx_WrBuff { 
          bins write = {1}; 
          bins no_write = {0}; 
        }
        Rx_EoF : coverpoint uin_hdlc.Rx_EoF { 
          bins eof = {1}; 
          bins not_eof = {0}; 
        }
        Rx_FrameSize : coverpoint uin_hdlc.Rx_FrameSize { 
          bins size[] = {[7:0]}; 
        }
        Rx_Overflow : coverpoint uin_hdlc.Rx_Overflow { 
          bins overflow = {1}; 
          bins no_overflow = {0}; 
        }
        Rx_FCSerr : coverpoint uin_hdlc.Rx_FCSerr { 
          bins err = {1}; 
          bins no_err = {0}; 
        }
        Rx_FCSen : coverpoint uin_hdlc.Rx_FCSen { 
          bins enabled = {1}; 
          bins disabled = {0}; 
        }
        Rx_DataBuffOut : coverpoint uin_hdlc.Rx_DataBuffOut { 
          bins data[] = {[7:0]}; 
        }
        Rx_RdBuff : coverpoint uin_hdlc.Rx_RdBuff { 
          bins read = {1}; 
          bins no_read = {0}; 
        }
        Rx_NewByte : coverpoint uin_hdlc.Rx_NewByte { 
          bins newbyte = {1}; 
          bins none = {0}; 
        }
        Rx_StartZeroDetect : coverpoint uin_hdlc.Rx_StartZeroDetect { 
          bins start = {1}; 
          bins no_start = {0}; 
        }
        Rx_FlagDetect : coverpoint uin_hdlc.Rx_FlagDetect { 
          bins flag = {1}; 
          bins no_flag = {0}; 
        }
        Rx_AbortDetect : coverpoint uin_hdlc.Rx_AbortDetect { 
          bins abort = {1}; 
          bins no_abort = {0}; 
        }
        Rx_FrameError : coverpoint uin_hdlc.Rx_FrameError { 
          bins error = {1}; 
          bins no_error = {0}; 
        }
        Rx_Drop : coverpoint uin_hdlc.Rx_Drop { 
          bins drop = {1}; 
          bins keep = {0}; 
        }
        Rx_StartFCS : coverpoint uin_hdlc.Rx_StartFCS { 
          bins start = {1}; 
          bins no_start = {0}; 
        }
        Rx_StopFCS : coverpoint uin_hdlc.Rx_StopFCS { 
          bins stop = {1}; 
          bins no_stop = {0}; 
        }
        RxD : coverpoint uin_hdlc.RxD { 
          bins one = {1}; 
          bins zero = {0}; 
        }
        ZeroDetect : coverpoint uin_hdlc.ZeroDetect { 
          bins detect = {1}; 
          bins none = {0}; 
        }
        // TX 
        Tx_AbortFrame : coverpoint uin_hdlc.Tx_AbortFrame { 
          bins abort = {1}; 
          bins no_abort = {0}; 
        }
        Tx_AbortedTrans : coverpoint uin_hdlc.Tx_AbortedTrans { 
          bins aborted = {1}; 
          bins not_aborted = {0}; 
        }
        Tx_DataAvail : coverpoint uin_hdlc.Tx_DataAvail { 
          bins avail = {1}; 
          bins not_avail = {0}; 
        }
        Tx_ValidFrame : coverpoint uin_hdlc.Tx_ValidFrame {
          bins invalid = {0};
          bins valid   = {1};
        }

        Tx_WriteFCS : coverpoint uin_hdlc.Tx_WriteFCS {
          bins no_write = {0};
          bins write    = {1};
        }

        Tx_InitZero : coverpoint uin_hdlc.Tx_InitZero {
          bins no_init = {0};
          bins init    = {1};
        }
        Tx_StartFCS : coverpoint uin_hdlc.Tx_StartFCS {
          bins no_start = {0};
          bins start    = {1};
        }
        Tx_RdBuff : coverpoint uin_hdlc.Tx_RdBuff {
          bins no_read = {0};
          bins read    = {1};
        }
        Tx_NewByte : coverpoint uin_hdlc.Tx_NewByte {
          bins nob = {0};
          bins newb  = {1};
        }
        Tx_FCSDone : coverpoint uin_hdlc.Tx_FCSDone {
          bins not_done = {0};
          bins done     = {1};
        }

        Tx_Data : coverpoint uin_hdlc.Tx_Data {
          bins data[] = {[7:0]};
        }
        Tx_Full : coverpoint uin_hdlc.Tx_Full {
          bins not_full = {0};
          bins full     = {1};
        }
        Tx_FrameSize : coverpoint uin_hdlc.Tx_FrameSize {
          bins size[] = {[7:0]};
        }
        Tx_DataOutBuff : coverpoint uin_hdlc.Tx_DataOutBuff {
          bins data[] = {[7:0]};
        }
        Tx_WrBuff : coverpoint uin_hdlc.Tx_WrBuff {
          bins no_write = {0};
          bins write    = {1};
        }
        Tx_Enable : coverpoint uin_hdlc.Tx_Enable {
          bins txdis = {0};
          bins txen  = {1};
        }
        Tx_DataInBuff : coverpoint uin_hdlc.Tx_DataInBuff {
          bins data[] = {[7:0]};
        }
  endgroup
  cg my_cg = new();
endprogram
