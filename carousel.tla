------------------------------- MODULE carousel -------------------------------

(***************************************************************************)
(* This is a TLA+ specification of the Carousel protocol.                  *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets, Sequences, TLC
CONSTANT C, N, T, NumOfMessages

ASSUME C \in Nat /\ C > 0
ASSUME N \in Nat /\ N > 0
Clients == 1..C
Nodes == 1..N

remove(i, seq) == [ j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j] ELSE seq[j+1] ]

(* --algorithm progress
variable
  IDSet = <<1..T>>,
  
  \* Status of each node
  status = [n \in Nodes |-> "Initiated"],
  
\*  TODO: Convert to matrix
  sent = [n \in Nodes |-> 0],
  received = [n \in Nodes |-> 0],
  \* Message queue
  queue = <<>>,
  channels = [n \in Nodes |-> <<>>],
  \* How many progress handlers have seen the switch from unprocessed to processed
  switchHappened = 0,
  \* The number of unacknowledged messages
  unacked = 0;

\* Queue macros
macro recv(queue, receiver)
begin
  await queue /= <<>>;
  receiver := Head(queue);
  queue := Tail(queue);
end macro

macro send(queue, message)
begin
  queue := Append(queue, message);
end macro

\* Message procedures
procedure createClientMsg(msg, client, serverSet)
variable
    tmp;
begin
  P1:
\*    Get ID from IDSet and remove it from IDSet
    tmp := Head(IDSet);
    IDSet := Tail(IDSet);
    msg := [ID |-> tmp, client |-> client, servers |-> serverSet];
end procedure

procedure createServerMsg(msg, id, serverStatus)
begin
  P1:
\*    Put ID back to IDSet
    IDSet := Append(IDSet, id);
    msg := [ID |-> id, serverStatus |-> serverStatus];
end procedure

\* Appends status to the progress set at Quorum nodes
procedure updateStatus(node)
variable 
    incoming = "";
begin
  P1:
    recv(channels[node], incoming);
  IncrementReceived:
    received[node] := received[node] + 1;
  Update:
    status[node] := incoming;
end procedure

procedure updateCounter(node)
variable 
    incoming = "";
begin
  P1:
    recv(channels[node], incoming);
    status[node] := incoming;
end procedure

procedure sendServerMessages(msg)
variable 
    incoming = ""; 
    toSend;
begin
  P0:
    serverSet := msg.serverSet;
  P1:
    while counter < NumOfMessages do
        with s \in serverSet do
            send(channels[s], "test");
            sent[client] := sent[client] + 1;
        end with;
    IncrementCounter:
        counter := counter + 1;
    end while;
end procedure

procedure sendMessagesToSubset(client, serverSet)
variable 
    msg;
begin
  P0:
    call createClientMsg(msg, client, serverSet);
  P1:
    call sendServerMessages(msg);
end procedure


fair process loadChannels \in Clients
variables
    counter = 0,
    subsets = SUBSET Nodes,
    chosen = {};
begin
    P0: 
        with chonsen \in subsets do
            call sendMessagesToSubset(self, chosen);
        end with;
end process;


fair process nodeHandler \in Nodes
variable
  message = "";
begin P0:
  print self;
  test:
  while channels[self] # <<>> do
  Write:
    call updateStatus(self);
  end while;

end process;

end algorithm *)
\* BEGIN TRANSLATION
\* Label P1 of procedure createClientMsg at line 55 col 5 changed to P1_
\* Label P1 of procedure createServerMsg at line 64 col 5 changed to P1_c
\* Label P1 of procedure updateStatus at line 38 col 3 changed to P1_u
\* Label P1 of procedure updateCounter at line 38 col 3 changed to P1_up
\* Label P0 of procedure sendServerMessages at line 97 col 5 changed to P0_
\* Label P1 of procedure sendServerMessages at line 99 col 5 changed to P1_s
\* Label P0 of procedure sendMessagesToSubset at line 114 col 5 changed to P0_s
\* Label P0 of process loadChannels at line 127 col 9 changed to P0_l
\* Procedure variable incoming of procedure updateStatus at line 71 col 5 changed to incoming_
\* Procedure variable incoming of procedure updateCounter at line 84 col 5 changed to incoming_u
\* Procedure variable msg of procedure sendMessagesToSubset at line 111 col 5 changed to msg_
\* Parameter msg of procedure createClientMsg at line 49 col 27 changed to msg_c
\* Parameter client of procedure createClientMsg at line 49 col 32 changed to client_
\* Parameter serverSet of procedure createClientMsg at line 49 col 40 changed to serverSet_
\* Parameter msg of procedure createServerMsg at line 60 col 27 changed to msg_cr
\* Parameter node of procedure updateStatus at line 69 col 24 changed to node_
CONSTANT defaultInitValue
VARIABLES IDSet, status, sent, received, queue, channels, switchHappened, 
          unacked, pc, stack, msg_c, client_, serverSet_, tmp, msg_cr, id, 
          serverStatus, node_, incoming_, node, incoming_u, msg, incoming, 
          toSend, client, serverSet, msg_, counter, subsets, chosen, message

vars == << IDSet, status, sent, received, queue, channels, switchHappened, 
           unacked, pc, stack, msg_c, client_, serverSet_, tmp, msg_cr, id, 
           serverStatus, node_, incoming_, node, incoming_u, msg, incoming, 
           toSend, client, serverSet, msg_, counter, subsets, chosen, message
        >>

ProcSet == (Clients) \cup (Nodes)

Init == (* Global variables *)
        /\ IDSet = <<1..T>>
        /\ status = [n \in Nodes |-> "Initiated"]
        /\ sent = [n \in Nodes |-> 0]
        /\ received = [n \in Nodes |-> 0]
        /\ queue = <<>>
        /\ channels = [n \in Nodes |-> <<>>]
        /\ switchHappened = 0
        /\ unacked = 0
        (* Procedure createClientMsg *)
        /\ msg_c = [ self \in ProcSet |-> defaultInitValue]
        /\ client_ = [ self \in ProcSet |-> defaultInitValue]
        /\ serverSet_ = [ self \in ProcSet |-> defaultInitValue]
        /\ tmp = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure createServerMsg *)
        /\ msg_cr = [ self \in ProcSet |-> defaultInitValue]
        /\ id = [ self \in ProcSet |-> defaultInitValue]
        /\ serverStatus = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure updateStatus *)
        /\ node_ = [ self \in ProcSet |-> defaultInitValue]
        /\ incoming_ = [ self \in ProcSet |-> ""]
        (* Procedure updateCounter *)
        /\ node = [ self \in ProcSet |-> defaultInitValue]
        /\ incoming_u = [ self \in ProcSet |-> ""]
        (* Procedure sendServerMessages *)
        /\ msg = [ self \in ProcSet |-> defaultInitValue]
        /\ incoming = [ self \in ProcSet |-> ""]
        /\ toSend = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure sendMessagesToSubset *)
        /\ client = [ self \in ProcSet |-> defaultInitValue]
        /\ serverSet = [ self \in ProcSet |-> defaultInitValue]
        /\ msg_ = [ self \in ProcSet |-> defaultInitValue]
        (* Process loadChannels *)
        /\ counter = [self \in Clients |-> 0]
        /\ subsets = [self \in Clients |-> SUBSET Nodes]
        /\ chosen = [self \in Clients |-> {}]
        (* Process nodeHandler *)
        /\ message = [self \in Nodes |-> ""]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "P0_l"
                                        [] self \in Nodes -> "P0"]

P1_(self) == /\ pc[self] = "P1_"
             /\ tmp' = [tmp EXCEPT ![self] = Head(IDSet)]
             /\ IDSet' = Tail(IDSet)
             /\ msg_c' = [msg_c EXCEPT ![self] = [ID |-> tmp'[self], client |-> client_[self], servers |-> serverSet_[self]]]
             /\ pc' = [pc EXCEPT ![self] = "Error"]
             /\ UNCHANGED << status, sent, received, queue, channels, 
                             switchHappened, unacked, stack, client_, 
                             serverSet_, msg_cr, id, serverStatus, node_, 
                             incoming_, node, incoming_u, msg, incoming, 
                             toSend, client, serverSet, msg_, counter, subsets, 
                             chosen, message >>

createClientMsg(self) == P1_(self)

P1_c(self) == /\ pc[self] = "P1_c"
              /\ IDSet' = Append(IDSet, id[self])
              /\ msg_cr' = [msg_cr EXCEPT ![self] = [ID |-> id[self], serverStatus |-> serverStatus[self]]]
              /\ pc' = [pc EXCEPT ![self] = "Error"]
              /\ UNCHANGED << status, sent, received, queue, channels, 
                              switchHappened, unacked, stack, msg_c, client_, 
                              serverSet_, tmp, id, serverStatus, node_, 
                              incoming_, node, incoming_u, msg, incoming, 
                              toSend, client, serverSet, msg_, counter, 
                              subsets, chosen, message >>

createServerMsg(self) == P1_c(self)

P1_u(self) == /\ pc[self] = "P1_u"
              /\ (channels[node_[self]]) /= <<>>
              /\ incoming_' = [incoming_ EXCEPT ![self] = Head((channels[node_[self]]))]
              /\ channels' = [channels EXCEPT ![node_[self]] = Tail((channels[node_[self]]))]
              /\ PrintT(<<"hey", incoming_'[self]>>)
              /\ pc' = [pc EXCEPT ![self] = "IncrementReceived"]
              /\ UNCHANGED << IDSet, status, sent, received, queue, 
                              switchHappened, unacked, stack, msg_c, client_, 
                              serverSet_, tmp, msg_cr, id, serverStatus, node_, 
                              node, incoming_u, msg, incoming, toSend, client, 
                              serverSet, msg_, counter, subsets, chosen, 
                              message >>

IncrementReceived(self) == /\ pc[self] = "IncrementReceived"
                           /\ received' = [received EXCEPT ![node_[self]] = received[node_[self]] + 1]
                           /\ pc' = [pc EXCEPT ![self] = "Update"]
                           /\ UNCHANGED << IDSet, status, sent, queue, 
                                           channels, switchHappened, unacked, 
                                           stack, msg_c, client_, serverSet_, 
                                           tmp, msg_cr, id, serverStatus, 
                                           node_, incoming_, node, incoming_u, 
                                           msg, incoming, toSend, client, 
                                           serverSet, msg_, counter, subsets, 
                                           chosen, message >>

Update(self) == /\ pc[self] = "Update"
                /\ status' = [status EXCEPT ![node_[self]] = incoming_[self]]
                /\ pc' = [pc EXCEPT ![self] = "Error"]
                /\ UNCHANGED << IDSet, sent, received, queue, channels, 
                                switchHappened, unacked, stack, msg_c, client_, 
                                serverSet_, tmp, msg_cr, id, serverStatus, 
                                node_, incoming_, node, incoming_u, msg, 
                                incoming, toSend, client, serverSet, msg_, 
                                counter, subsets, chosen, message >>

updateStatus(self) == P1_u(self) \/ IncrementReceived(self) \/ Update(self)

P1_up(self) == /\ pc[self] = "P1_up"
               /\ (channels[node[self]]) /= <<>>
               /\ incoming_u' = [incoming_u EXCEPT ![self] = Head((channels[node[self]]))]
               /\ channels' = [channels EXCEPT ![node[self]] = Tail((channels[node[self]]))]
               /\ status' = [status EXCEPT ![node[self]] = incoming_u'[self]]
               /\ pc' = [pc EXCEPT ![self] = "Error"]
               /\ UNCHANGED << IDSet, sent, received, queue, switchHappened, 
                               unacked, stack, msg_c, client_, serverSet_, tmp, 
                               msg_cr, id, serverStatus, node_, incoming_, 
                               node, msg, incoming, toSend, client, serverSet, 
                               msg_, counter, subsets, chosen, message >>

updateCounter(self) == P1_up(self)

P0_(self) == /\ pc[self] = "P0_"
             /\ serverSet' = [serverSet EXCEPT ![self] = msg[self].serverSet]
             /\ pc' = [pc EXCEPT ![self] = "P1_s"]
             /\ UNCHANGED << IDSet, status, sent, received, queue, channels, 
                             switchHappened, unacked, stack, msg_c, client_, 
                             serverSet_, tmp, msg_cr, id, serverStatus, node_, 
                             incoming_, node, incoming_u, msg, incoming, 
                             toSend, client, msg_, counter, subsets, chosen, 
                             message >>

P1_s(self) == /\ pc[self] = "P1_s"
              /\ IF counter[self] < NumOfMessages
                    THEN /\ \E s \in serverSet[self]:
                              /\ channels' = [channels EXCEPT ![s] = Append((channels[s]), "test")]
                              /\ sent' = [sent EXCEPT ![client[self]] = sent[client[self]] + 1]
                         /\ pc' = [pc EXCEPT ![self] = "IncrementCounter"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Error"]
                         /\ UNCHANGED << sent, channels >>
              /\ UNCHANGED << IDSet, status, received, queue, switchHappened, 
                              unacked, stack, msg_c, client_, serverSet_, tmp, 
                              msg_cr, id, serverStatus, node_, incoming_, node, 
                              incoming_u, msg, incoming, toSend, client, 
                              serverSet, msg_, counter, subsets, chosen, 
                              message >>

IncrementCounter(self) == /\ pc[self] = "IncrementCounter"
                          /\ counter' = [counter EXCEPT ![self] = counter[self] + 1]
                          /\ pc' = [pc EXCEPT ![self] = "P1_s"]
                          /\ UNCHANGED << IDSet, status, sent, received, queue, 
                                          channels, switchHappened, unacked, 
                                          stack, msg_c, client_, serverSet_, 
                                          tmp, msg_cr, id, serverStatus, node_, 
                                          incoming_, node, incoming_u, msg, 
                                          incoming, toSend, client, serverSet, 
                                          msg_, subsets, chosen, message >>

sendServerMessages(self) == P0_(self) \/ P1_s(self)
                               \/ IncrementCounter(self)

P0_s(self) == /\ pc[self] = "P0_s"
              /\ /\ client_' = [client_ EXCEPT ![self] = client[self]]
                 /\ msg_c' = [msg_c EXCEPT ![self] = msg_[self]]
                 /\ serverSet_' = [serverSet_ EXCEPT ![self] = serverSet[self]]
                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "createClientMsg",
                                                          pc        |->  "P1",
                                                          tmp       |->  tmp[self],
                                                          msg_c     |->  msg_c[self],
                                                          client_   |->  client_[self],
                                                          serverSet_ |->  serverSet_[self] ] >>
                                                      \o stack[self]]
              /\ tmp' = [tmp EXCEPT ![self] = defaultInitValue]
              /\ pc' = [pc EXCEPT ![self] = "P1_"]
              /\ UNCHANGED << IDSet, status, sent, received, queue, channels, 
                              switchHappened, unacked, msg_cr, id, 
                              serverStatus, node_, incoming_, node, incoming_u, 
                              msg, incoming, toSend, client, serverSet, msg_, 
                              counter, subsets, chosen, message >>

P1(self) == /\ pc[self] = "P1"
            /\ /\ msg' = [msg EXCEPT ![self] = msg_[self]]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "sendServerMessages",
                                                        pc        |->  "Error",
                                                        incoming  |->  incoming[self],
                                                        toSend    |->  toSend[self],
                                                        msg       |->  msg[self] ] >>
                                                    \o stack[self]]
            /\ incoming' = [incoming EXCEPT ![self] = ""]
            /\ toSend' = [toSend EXCEPT ![self] = defaultInitValue]
            /\ pc' = [pc EXCEPT ![self] = "P0_"]
            /\ UNCHANGED << IDSet, status, sent, received, queue, channels, 
                            switchHappened, unacked, msg_c, client_, 
                            serverSet_, tmp, msg_cr, id, serverStatus, node_, 
                            incoming_, node, incoming_u, client, serverSet, 
                            msg_, counter, subsets, chosen, message >>

sendMessagesToSubset(self) == P0_s(self) \/ P1(self)

P0_l(self) == /\ pc[self] = "P0_l"
              /\ \E chonsen \in subsets[self]:
                   /\ /\ client' = [client EXCEPT ![self] = self]
                      /\ serverSet' = [serverSet EXCEPT ![self] = chosen[self]]
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "sendMessagesToSubset",
                                                               pc        |->  "Done",
                                                               msg_      |->  msg_[self],
                                                               client    |->  client[self],
                                                               serverSet |->  serverSet[self] ] >>
                                                           \o stack[self]]
                   /\ msg_' = [msg_ EXCEPT ![self] = defaultInitValue]
                   /\ pc' = [pc EXCEPT ![self] = "P0_s"]
              /\ UNCHANGED << IDSet, status, sent, received, queue, channels, 
                              switchHappened, unacked, msg_c, client_, 
                              serverSet_, tmp, msg_cr, id, serverStatus, node_, 
                              incoming_, node, incoming_u, msg, incoming, 
                              toSend, counter, subsets, chosen, message >>

loadChannels(self) == P0_l(self)

P0(self) == /\ pc[self] = "P0"
            /\ PrintT(self)
            /\ pc' = [pc EXCEPT ![self] = "test"]
            /\ UNCHANGED << IDSet, status, sent, received, queue, channels, 
                            switchHappened, unacked, stack, msg_c, client_, 
                            serverSet_, tmp, msg_cr, id, serverStatus, node_, 
                            incoming_, node, incoming_u, msg, incoming, toSend, 
                            client, serverSet, msg_, counter, subsets, chosen, 
                            message >>

test(self) == /\ pc[self] = "test"
              /\ IF channels[self] # <<>>
                    THEN /\ pc' = [pc EXCEPT ![self] = "Write"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << IDSet, status, sent, received, queue, channels, 
                              switchHappened, unacked, stack, msg_c, client_, 
                              serverSet_, tmp, msg_cr, id, serverStatus, node_, 
                              incoming_, node, incoming_u, msg, incoming, 
                              toSend, client, serverSet, msg_, counter, 
                              subsets, chosen, message >>

Write(self) == /\ pc[self] = "Write"
               /\ /\ node_' = [node_ EXCEPT ![self] = self]
                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "updateStatus",
                                                           pc        |->  "test",
                                                           incoming_ |->  incoming_[self],
                                                           node_     |->  node_[self] ] >>
                                                       \o stack[self]]
               /\ incoming_' = [incoming_ EXCEPT ![self] = ""]
               /\ pc' = [pc EXCEPT ![self] = "P1_u"]
               /\ UNCHANGED << IDSet, status, sent, received, queue, channels, 
                               switchHappened, unacked, msg_c, client_, 
                               serverSet_, tmp, msg_cr, id, serverStatus, node, 
                               incoming_u, msg, incoming, toSend, client, 
                               serverSet, msg_, counter, subsets, chosen, 
                               message >>

nodeHandler(self) == P0(self) \/ test(self) \/ Write(self)

Next == (\E self \in ProcSet:  \/ createClientMsg(self)
                               \/ createServerMsg(self)
                               \/ updateStatus(self) \/ updateCounter(self)
                               \/ sendServerMessages(self)
                               \/ sendMessagesToSubset(self))
           \/ (\E self \in Clients: loadChannels(self))
           \/ (\E self \in Nodes: nodeHandler(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Clients : /\ WF_vars(loadChannels(self))
                                 /\ WF_vars(sendMessagesToSubset(self))
                                 /\ WF_vars(createClientMsg(self))
                                 /\ WF_vars(sendServerMessages(self))
        /\ \A self \in Nodes : WF_vars(nodeHandler(self)) /\ WF_vars(updateStatus(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


\* Invariants
StatusInvariant == \A x \in 1..N:
                status[x] = "Committed" \/ status[x] = "Aborted" \/ status[x] = "Prepared" \/ status[x] = "Initiated"
                
SentReceivedInvariant == \A x \in 1..N:
                sent[x] <= NumOfMessages /\ received[x] <= NumOfMessages /\ sent[x] < received[x]
                
\* Correctness
CounterCorrectness == <>(Termination /\ (\A x \in 1..N: sent[x] = NumOfMessages /\ received[x] = NumOfMessages))

=================================
