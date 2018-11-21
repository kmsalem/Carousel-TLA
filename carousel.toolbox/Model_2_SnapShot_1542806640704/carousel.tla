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

(* --algorithm progress
variable
  IDSet = <<1..T>>,
  
  \* Status of each node
  status = [n \in Nodes |-> "Init"],
  
  sent = [n \in Nodes |-> 0],
  received = [n \in Nodes |-> 0],
  channels = [n \in Nodes |-> <<>>],

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


\* Client
procedure createClientMsg(msg, client)
variable
    tmp;
begin
  P1:
\*    Get ID from IDSet and remove it from IDSet
    await IDSet # <<>>;  \* First check if IDSet is empty, if not, wait
    tmp := Head(IDSet);
    IDSet := Tail(IDSet);
    msg := [id |-> tmp, client |-> client];
end procedure


procedure createServerMsg(msg, id, serverStatus)
begin
  P1:
\*    Put ID back to IDSet
    IDSet := Append(IDSet, id);
    msg := [id |-> id, serverStatus |-> serverStatus];
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


procedure sendClientMessagesToServers(client, serverSet)
variable 
    msg;
begin
  P0:
    while serverSet # <<>> do
        with selectedServer \in serverSet do
\*            Removed selected from serverSet
            serverSet := serverSet \ {selectedServer};
            call createClientMsg(msg, client);
        end with;
    end while;
end procedure


fair process sendClientMessages \in Clients
variables
    counter = 0,
    subsets = SUBSET Nodes;
begin
    P0:
        with chosen \in subsets do
            call sendClientMessagesToServers(self, chosen);
        end with;
end process;


fair process nodeHandler \in Nodes
variable
  message = "";
begin
  test:
  await channels[self] # <<>>;
  call updateStatus(self);

end process;

end algorithm *)
\* BEGIN TRANSLATION
\* Label P1 of procedure createClientMsg at line 47 col 5 changed to P1_
\* Label P1 of procedure createServerMsg at line 58 col 5 changed to P1_c
\* Label P1 of procedure updateStatus at line 29 col 3 changed to P1_u
\* Label P1 of procedure updateCounter at line 29 col 3 changed to P1_up
\* Label P0 of procedure sendServerMessages at line 93 col 5 changed to P0_
\* Label P0 of procedure sendClientMessagesToServers at line 111 col 5 changed to P0_s
\* Procedure variable incoming of procedure updateStatus at line 66 col 5 changed to incoming_
\* Procedure variable incoming of procedure updateCounter at line 79 col 5 changed to incoming_u
\* Procedure variable msg of procedure sendClientMessagesToServers at line 108 col 5 changed to msg_
\* Parameter msg of procedure createClientMsg at line 41 col 27 changed to msg_c
\* Parameter client of procedure createClientMsg at line 41 col 32 changed to client_
\* Parameter msg of procedure createServerMsg at line 54 col 27 changed to msg_cr
\* Parameter node of procedure updateStatus at line 64 col 24 changed to node_
CONSTANT defaultInitValue
VARIABLES IDSet, status, sent, received, channels, pc, stack, msg_c, client_, 
          tmp, msg_cr, id, serverStatus, node_, incoming_, node, incoming_u, 
          msg, incoming, toSend, client, serverSet, msg_, counter, subsets, 
          message

vars == << IDSet, status, sent, received, channels, pc, stack, msg_c, client_, 
           tmp, msg_cr, id, serverStatus, node_, incoming_, node, incoming_u, 
           msg, incoming, toSend, client, serverSet, msg_, counter, subsets, 
           message >>

ProcSet == (Clients) \cup (Nodes)

Init == (* Global variables *)
        /\ IDSet = <<1..T>>
        /\ status = [n \in Nodes |-> "Init"]
        /\ sent = [n \in Nodes |-> 0]
        /\ received = [n \in Nodes |-> 0]
        /\ channels = [n \in Nodes |-> <<>>]
        (* Procedure createClientMsg *)
        /\ msg_c = [ self \in ProcSet |-> defaultInitValue]
        /\ client_ = [ self \in ProcSet |-> defaultInitValue]
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
        (* Procedure sendClientMessagesToServers *)
        /\ client = [ self \in ProcSet |-> defaultInitValue]
        /\ serverSet = [ self \in ProcSet |-> defaultInitValue]
        /\ msg_ = [ self \in ProcSet |-> defaultInitValue]
        (* Process sendClientMessages *)
        /\ counter = [self \in Clients |-> 0]
        /\ subsets = [self \in Clients |-> SUBSET Nodes]
        (* Process nodeHandler *)
        /\ message = [self \in Nodes |-> ""]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "P0"
                                        [] self \in Nodes -> "test"]

P1_(self) == /\ pc[self] = "P1_"
             /\ IDSet # <<>>
             /\ tmp' = [tmp EXCEPT ![self] = Head(IDSet)]
             /\ IDSet' = Tail(IDSet)
             /\ msg_c' = [msg_c EXCEPT ![self] = [id |-> tmp'[self], client |-> client_[self]]]
             /\ pc' = [pc EXCEPT ![self] = "Error"]
             /\ UNCHANGED << status, sent, received, channels, stack, client_, 
                             msg_cr, id, serverStatus, node_, incoming_, node, 
                             incoming_u, msg, incoming, toSend, client, 
                             serverSet, msg_, counter, subsets, message >>

createClientMsg(self) == P1_(self)

P1_c(self) == /\ pc[self] = "P1_c"
              /\ IDSet' = Append(IDSet, id[self])
              /\ msg_cr' = [msg_cr EXCEPT ![self] = [id |-> id[self], serverStatus |-> serverStatus[self]]]
              /\ pc' = [pc EXCEPT ![self] = "Error"]
              /\ UNCHANGED << status, sent, received, channels, stack, msg_c, 
                              client_, tmp, id, serverStatus, node_, incoming_, 
                              node, incoming_u, msg, incoming, toSend, client, 
                              serverSet, msg_, counter, subsets, message >>

createServerMsg(self) == P1_c(self)

P1_u(self) == /\ pc[self] = "P1_u"
              /\ (channels[node_[self]]) /= <<>>
              /\ incoming_' = [incoming_ EXCEPT ![self] = Head((channels[node_[self]]))]
              /\ channels' = [channels EXCEPT ![node_[self]] = Tail((channels[node_[self]]))]
              /\ pc' = [pc EXCEPT ![self] = "IncrementReceived"]
              /\ UNCHANGED << IDSet, status, sent, received, stack, msg_c, 
                              client_, tmp, msg_cr, id, serverStatus, node_, 
                              node, incoming_u, msg, incoming, toSend, client, 
                              serverSet, msg_, counter, subsets, message >>

IncrementReceived(self) == /\ pc[self] = "IncrementReceived"
                           /\ received' = [received EXCEPT ![node_[self]] = received[node_[self]] + 1]
                           /\ pc' = [pc EXCEPT ![self] = "Update"]
                           /\ UNCHANGED << IDSet, status, sent, channels, 
                                           stack, msg_c, client_, tmp, msg_cr, 
                                           id, serverStatus, node_, incoming_, 
                                           node, incoming_u, msg, incoming, 
                                           toSend, client, serverSet, msg_, 
                                           counter, subsets, message >>

Update(self) == /\ pc[self] = "Update"
                /\ status' = [status EXCEPT ![node_[self]] = incoming_[self]]
                /\ pc' = [pc EXCEPT ![self] = "Error"]
                /\ UNCHANGED << IDSet, sent, received, channels, stack, msg_c, 
                                client_, tmp, msg_cr, id, serverStatus, node_, 
                                incoming_, node, incoming_u, msg, incoming, 
                                toSend, client, serverSet, msg_, counter, 
                                subsets, message >>

updateStatus(self) == P1_u(self) \/ IncrementReceived(self) \/ Update(self)

P1_up(self) == /\ pc[self] = "P1_up"
               /\ (channels[node[self]]) /= <<>>
               /\ incoming_u' = [incoming_u EXCEPT ![self] = Head((channels[node[self]]))]
               /\ channels' = [channels EXCEPT ![node[self]] = Tail((channels[node[self]]))]
               /\ status' = [status EXCEPT ![node[self]] = incoming_u'[self]]
               /\ pc' = [pc EXCEPT ![self] = "Error"]
               /\ UNCHANGED << IDSet, sent, received, stack, msg_c, client_, 
                               tmp, msg_cr, id, serverStatus, node_, incoming_, 
                               node, msg, incoming, toSend, client, serverSet, 
                               msg_, counter, subsets, message >>

updateCounter(self) == P1_up(self)

P0_(self) == /\ pc[self] = "P0_"
             /\ serverSet' = [serverSet EXCEPT ![self] = msg[self].serverSet]
             /\ pc' = [pc EXCEPT ![self] = "P1"]
             /\ UNCHANGED << IDSet, status, sent, received, channels, stack, 
                             msg_c, client_, tmp, msg_cr, id, serverStatus, 
                             node_, incoming_, node, incoming_u, msg, incoming, 
                             toSend, client, msg_, counter, subsets, message >>

P1(self) == /\ pc[self] = "P1"
            /\ IF counter[self] < NumOfMessages
                  THEN /\ \E s \in serverSet[self]:
                            /\ channels' = [channels EXCEPT ![s] = Append((channels[s]), "test")]
                            /\ sent' = [sent EXCEPT ![client[self]] = sent[client[self]] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "IncrementCounter"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Error"]
                       /\ UNCHANGED << sent, channels >>
            /\ UNCHANGED << IDSet, status, received, stack, msg_c, client_, 
                            tmp, msg_cr, id, serverStatus, node_, incoming_, 
                            node, incoming_u, msg, incoming, toSend, client, 
                            serverSet, msg_, counter, subsets, message >>

IncrementCounter(self) == /\ pc[self] = "IncrementCounter"
                          /\ counter' = [counter EXCEPT ![self] = counter[self] + 1]
                          /\ pc' = [pc EXCEPT ![self] = "P1"]
                          /\ UNCHANGED << IDSet, status, sent, received, 
                                          channels, stack, msg_c, client_, tmp, 
                                          msg_cr, id, serverStatus, node_, 
                                          incoming_, node, incoming_u, msg, 
                                          incoming, toSend, client, serverSet, 
                                          msg_, subsets, message >>

sendServerMessages(self) == P0_(self) \/ P1(self) \/ IncrementCounter(self)

P0_s(self) == /\ pc[self] = "P0_s"
              /\ IF serverSet[self] # <<>>
                    THEN /\ \E selectedServer \in serverSet[self]:
                              /\ serverSet' = [serverSet EXCEPT ![self] = serverSet[self] \ {selectedServer}]
                              /\ /\ client_' = [client_ EXCEPT ![self] = client[self]]
                                 /\ msg_c' = [msg_c EXCEPT ![self] = msg_[self]]
                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "createClientMsg",
                                                                          pc        |->  "P0_s",
                                                                          tmp       |->  tmp[self],
                                                                          msg_c     |->  msg_c[self],
                                                                          client_   |->  client_[self] ] >>
                                                                      \o stack[self]]
                              /\ tmp' = [tmp EXCEPT ![self] = defaultInitValue]
                              /\ pc' = [pc EXCEPT ![self] = "P1_"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Error"]
                         /\ UNCHANGED << stack, msg_c, client_, tmp, serverSet >>
              /\ UNCHANGED << IDSet, status, sent, received, channels, msg_cr, 
                              id, serverStatus, node_, incoming_, node, 
                              incoming_u, msg, incoming, toSend, client, msg_, 
                              counter, subsets, message >>

sendClientMessagesToServers(self) == P0_s(self)

P0(self) == /\ pc[self] = "P0"
            /\ \E chosen \in subsets[self]:
                 /\ /\ client' = [client EXCEPT ![self] = self]
                    /\ serverSet' = [serverSet EXCEPT ![self] = chosen]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "sendClientMessagesToServers",
                                                             pc        |->  "Done",
                                                             msg_      |->  msg_[self],
                                                             client    |->  client[self],
                                                             serverSet |->  serverSet[self] ] >>
                                                         \o stack[self]]
                 /\ msg_' = [msg_ EXCEPT ![self] = defaultInitValue]
                 /\ pc' = [pc EXCEPT ![self] = "P0_s"]
            /\ UNCHANGED << IDSet, status, sent, received, channels, msg_c, 
                            client_, tmp, msg_cr, id, serverStatus, node_, 
                            incoming_, node, incoming_u, msg, incoming, toSend, 
                            counter, subsets, message >>

sendClientMessages(self) == P0(self)

test(self) == /\ pc[self] = "test"
              /\ channels[self] # <<>>
              /\ /\ node_' = [node_ EXCEPT ![self] = self]
                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "updateStatus",
                                                          pc        |->  "Done",
                                                          incoming_ |->  incoming_[self],
                                                          node_     |->  node_[self] ] >>
                                                      \o stack[self]]
              /\ incoming_' = [incoming_ EXCEPT ![self] = ""]
              /\ pc' = [pc EXCEPT ![self] = "P1_u"]
              /\ UNCHANGED << IDSet, status, sent, received, channels, msg_c, 
                              client_, tmp, msg_cr, id, serverStatus, node, 
                              incoming_u, msg, incoming, toSend, client, 
                              serverSet, msg_, counter, subsets, message >>

nodeHandler(self) == test(self)

Next == (\E self \in ProcSet:  \/ createClientMsg(self)
                               \/ createServerMsg(self)
                               \/ updateStatus(self) \/ updateCounter(self)
                               \/ sendServerMessages(self)
                               \/ sendClientMessagesToServers(self))
           \/ (\E self \in Clients: sendClientMessages(self))
           \/ (\E self \in Nodes: nodeHandler(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Clients : /\ WF_vars(sendClientMessages(self))
                                 /\ WF_vars(sendClientMessagesToServers(self))
                                 /\ WF_vars(createClientMsg(self))
        /\ \A self \in Nodes : WF_vars(nodeHandler(self)) /\ WF_vars(updateStatus(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* Invariants
\*StatusInvariant == \A x \in 1..N:
\*                status[x] = "Committed" \/ status[x] = "Aborted" \/ status[x] = "Prepared" \/ status[x] = "Initiated"
\*                
\*SentReceivedInvariant == \A x \in 1..N:
\*                sent[x] <= NumOfMessages /\ received[x] <= NumOfMessages /\ sent[x] < received[x]
\*                
\*\* Correctness
\*CounterCorrectness == <>(Termination /\ (\A x \in 1..N: sent[x] = NumOfMessages /\ received[x] = NumOfMessages))

=================================
