------------------------------- MODULE carousel -------------------------------

(***************************************************************************)
(* This is a TLA+ specification of the Carousel protocol.                  *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets, Sequences, TLC
CONSTANT C, N, NumOfMessages

ASSUME C \in Nat /\ C > 0
ASSUME N \in Nat /\ N > 0
Clients == 1..C
Nodes == 1..N

(* --algorithm progress
variable
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
  print<<"hey", message>>;
end macro


\* Appends status to the progress set at Quorum nodes
procedure updateStatus(node)
variable 
    incoming = "";
begin
  P1:
    recv(channels[node], incoming);
    print<<"hey", incoming>>;
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

procedure sendMessages(node)
variable 
    incoming = "";
begin
  P0:
    while counter < NumOfMessages do
    Send:
        either send(channels[node], "Committed")
            or send(channels[node], "Aborted")
            or send(channels[node], "Prepared")
        end either;
        sent[node] := sent[node] + 1;
    IncrementCounter:
        counter := counter + 1;
    end while;
end procedure

procedure sendMessagesToSubset(chosen)
variable 
    incoming = "";
begin
  P0:
    while chosen # {} do
        with toSend \in chosen do
            chosen := chosen \ {toSend};
            call sendMessages(toSend);
        end with;
    end while;
end procedure


fair process loadChannels \in Clients
variables
    counter = 0,
    subsets = SUBSET Nodes,
    chosen = {};
begin
    P0: 
        with chonsen \in subsets do
            call sendMessagesToSubset(chosen);
        end with;
end process;


fair process nodeHandler \in Nodes
variable
  message = "";
begin P0:
  while channels[self] # <<>> do
  Write:
    call updateStatus(self);
  end while;

end process;

end algorithm *)
\* BEGIN TRANSLATION
\* Label P1 of procedure updateStatus at line 35 col 3 changed to P1_
\* Label P0 of procedure sendMessages at line 75 col 5 changed to P0_
\* Label P0 of procedure sendMessagesToSubset at line 92 col 5 changed to P0_s
\* Label P0 of process loadChannels at line 108 col 9 changed to P0_l
\* Process variable chosen of process loadChannels at line 105 col 5 changed to chosen_
\* Procedure variable incoming of procedure updateStatus at line 50 col 5 changed to incoming_
\* Procedure variable incoming of procedure updateCounter at line 63 col 5 changed to incoming_u
\* Procedure variable incoming of procedure sendMessages at line 72 col 5 changed to incoming_s
\* Parameter node of procedure updateStatus at line 48 col 24 changed to node_
\* Parameter node of procedure updateCounter at line 61 col 25 changed to node_u
CONSTANT defaultInitValue
VARIABLES status, sent, received, queue, channels, switchHappened, unacked, 
          pc, stack, node_, incoming_, node_u, incoming_u, node, incoming_s, 
          chosen, incoming, counter, subsets, chosen_, message

vars == << status, sent, received, queue, channels, switchHappened, unacked, 
           pc, stack, node_, incoming_, node_u, incoming_u, node, incoming_s, 
           chosen, incoming, counter, subsets, chosen_, message >>

ProcSet == (Clients) \cup (Nodes)

Init == (* Global variables *)
        /\ status = [n \in Nodes |-> "Initiated"]
        /\ sent = [n \in Nodes |-> 0]
        /\ received = [n \in Nodes |-> 0]
        /\ queue = <<>>
        /\ channels = [n \in Nodes |-> <<>>]
        /\ switchHappened = 0
        /\ unacked = 0
        (* Procedure updateStatus *)
        /\ node_ = [ self \in ProcSet |-> defaultInitValue]
        /\ incoming_ = [ self \in ProcSet |-> ""]
        (* Procedure updateCounter *)
        /\ node_u = [ self \in ProcSet |-> defaultInitValue]
        /\ incoming_u = [ self \in ProcSet |-> ""]
        (* Procedure sendMessages *)
        /\ node = [ self \in ProcSet |-> defaultInitValue]
        /\ incoming_s = [ self \in ProcSet |-> ""]
        (* Procedure sendMessagesToSubset *)
        /\ chosen = [ self \in ProcSet |-> defaultInitValue]
        /\ incoming = [ self \in ProcSet |-> ""]
        (* Process loadChannels *)
        /\ counter = [self \in Clients |-> 0]
        /\ subsets = [self \in Clients |-> SUBSET Nodes]
        /\ chosen_ = [self \in Clients |-> {}]
        (* Process nodeHandler *)
        /\ message = [self \in Nodes |-> ""]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "P0_l"
                                        [] self \in Nodes -> "P0"]

P1_(self) == /\ pc[self] = "P1_"
             /\ (channels[node_[self]]) /= <<>>
             /\ incoming_' = [incoming_ EXCEPT ![self] = Head((channels[node_[self]]))]
             /\ channels' = [channels EXCEPT ![node_[self]] = Tail((channels[node_[self]]))]
             /\ PrintT(<<"hey", incoming_'[self]>>)
             /\ pc' = [pc EXCEPT ![self] = "IncrementReceived"]
             /\ UNCHANGED << status, sent, received, queue, switchHappened, 
                             unacked, stack, node_, node_u, incoming_u, node, 
                             incoming_s, chosen, incoming, counter, subsets, 
                             chosen_, message >>

IncrementReceived(self) == /\ pc[self] = "IncrementReceived"
                           /\ received' = [received EXCEPT ![node_[self]] = received[node_[self]] + 1]
                           /\ pc' = [pc EXCEPT ![self] = "Update"]
                           /\ UNCHANGED << status, sent, queue, channels, 
                                           switchHappened, unacked, stack, 
                                           node_, incoming_, node_u, 
                                           incoming_u, node, incoming_s, 
                                           chosen, incoming, counter, subsets, 
                                           chosen_, message >>

Update(self) == /\ pc[self] = "Update"
                /\ status' = [status EXCEPT ![node_[self]] = incoming_[self]]
                /\ pc' = [pc EXCEPT ![self] = "Error"]
                /\ UNCHANGED << sent, received, queue, channels, 
                                switchHappened, unacked, stack, node_, 
                                incoming_, node_u, incoming_u, node, 
                                incoming_s, chosen, incoming, counter, subsets, 
                                chosen_, message >>

updateStatus(self) == P1_(self) \/ IncrementReceived(self) \/ Update(self)

P1(self) == /\ pc[self] = "P1"
            /\ (channels[node_u[self]]) /= <<>>
            /\ incoming_u' = [incoming_u EXCEPT ![self] = Head((channels[node_u[self]]))]
            /\ channels' = [channels EXCEPT ![node_u[self]] = Tail((channels[node_u[self]]))]
            /\ status' = [status EXCEPT ![node_u[self]] = incoming_u'[self]]
            /\ pc' = [pc EXCEPT ![self] = "Error"]
            /\ UNCHANGED << sent, received, queue, switchHappened, unacked, 
                            stack, node_, incoming_, node_u, node, incoming_s, 
                            chosen, incoming, counter, subsets, chosen_, 
                            message >>

updateCounter(self) == P1(self)

P0_(self) == /\ pc[self] = "P0_"
             /\ IF counter[self] < NumOfMessages
                   THEN /\ pc' = [pc EXCEPT ![self] = "Send"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "Error"]
             /\ UNCHANGED << status, sent, received, queue, channels, 
                             switchHappened, unacked, stack, node_, incoming_, 
                             node_u, incoming_u, node, incoming_s, chosen, 
                             incoming, counter, subsets, chosen_, message >>

Send(self) == /\ pc[self] = "Send"
              /\ \/ /\ channels' = [channels EXCEPT ![node[self]] = Append((channels[node[self]]), "Committed")]
                    /\ PrintT(<<"hey", "Committed">>)
                 \/ /\ channels' = [channels EXCEPT ![node[self]] = Append((channels[node[self]]), "Aborted")]
                    /\ PrintT(<<"hey", "Aborted">>)
                 \/ /\ channels' = [channels EXCEPT ![node[self]] = Append((channels[node[self]]), "Prepared")]
                    /\ PrintT(<<"hey", "Prepared">>)
              /\ sent' = [sent EXCEPT ![node[self]] = sent[node[self]] + 1]
              /\ pc' = [pc EXCEPT ![self] = "IncrementCounter"]
              /\ UNCHANGED << status, received, queue, switchHappened, unacked, 
                              stack, node_, incoming_, node_u, incoming_u, 
                              node, incoming_s, chosen, incoming, counter, 
                              subsets, chosen_, message >>

IncrementCounter(self) == /\ pc[self] = "IncrementCounter"
                          /\ counter' = [counter EXCEPT ![self] = counter[self] + 1]
                          /\ pc' = [pc EXCEPT ![self] = "P0_"]
                          /\ UNCHANGED << status, sent, received, queue, 
                                          channels, switchHappened, unacked, 
                                          stack, node_, incoming_, node_u, 
                                          incoming_u, node, incoming_s, chosen, 
                                          incoming, subsets, chosen_, message >>

sendMessages(self) == P0_(self) \/ Send(self) \/ IncrementCounter(self)

P0_s(self) == /\ pc[self] = "P0_s"
              /\ IF chosen[self] # {}
                    THEN /\ \E toSend \in chosen[self]:
                              /\ chosen' = [chosen EXCEPT ![self] = chosen[self] \ {toSend}]
                              /\ /\ node' = [node EXCEPT ![self] = toSend]
                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "sendMessages",
                                                                          pc        |->  "P0_s",
                                                                          incoming_s |->  incoming_s[self],
                                                                          node      |->  node[self] ] >>
                                                                      \o stack[self]]
                              /\ incoming_s' = [incoming_s EXCEPT ![self] = ""]
                              /\ pc' = [pc EXCEPT ![self] = "P0_"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Error"]
                         /\ UNCHANGED << stack, node, incoming_s, chosen >>
              /\ UNCHANGED << status, sent, received, queue, channels, 
                              switchHappened, unacked, node_, incoming_, 
                              node_u, incoming_u, incoming, counter, subsets, 
                              chosen_, message >>

sendMessagesToSubset(self) == P0_s(self)

P0_l(self) == /\ pc[self] = "P0_l"
              /\ \E chonsen \in subsets[self]:
                   /\ /\ chosen' = [chosen EXCEPT ![self] = chosen_[self]]
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "sendMessagesToSubset",
                                                               pc        |->  "Done",
                                                               incoming  |->  incoming[self],
                                                               chosen    |->  chosen[self] ] >>
                                                           \o stack[self]]
                   /\ incoming' = [incoming EXCEPT ![self] = ""]
                   /\ pc' = [pc EXCEPT ![self] = "P0_s"]
              /\ UNCHANGED << status, sent, received, queue, channels, 
                              switchHappened, unacked, node_, incoming_, 
                              node_u, incoming_u, node, incoming_s, counter, 
                              subsets, chosen_, message >>

loadChannels(self) == P0_l(self)

P0(self) == /\ pc[self] = "P0"
            /\ IF channels[self] # <<>>
                  THEN /\ pc' = [pc EXCEPT ![self] = "Write"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << status, sent, received, queue, channels, 
                            switchHappened, unacked, stack, node_, incoming_, 
                            node_u, incoming_u, node, incoming_s, chosen, 
                            incoming, counter, subsets, chosen_, message >>

Write(self) == /\ pc[self] = "Write"
               /\ /\ node_' = [node_ EXCEPT ![self] = self]
                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "updateStatus",
                                                           pc        |->  "P0",
                                                           incoming_ |->  incoming_[self],
                                                           node_     |->  node_[self] ] >>
                                                       \o stack[self]]
               /\ incoming_' = [incoming_ EXCEPT ![self] = ""]
               /\ pc' = [pc EXCEPT ![self] = "P1_"]
               /\ UNCHANGED << status, sent, received, queue, channels, 
                               switchHappened, unacked, node_u, incoming_u, 
                               node, incoming_s, chosen, incoming, counter, 
                               subsets, chosen_, message >>

nodeHandler(self) == P0(self) \/ Write(self)

Next == (\E self \in ProcSet:  \/ updateStatus(self) \/ updateCounter(self)
                               \/ sendMessages(self)
                               \/ sendMessagesToSubset(self))
           \/ (\E self \in Clients: loadChannels(self))
           \/ (\E self \in Nodes: nodeHandler(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Clients : /\ WF_vars(loadChannels(self))
                                 /\ WF_vars(sendMessagesToSubset(self))
                                 /\ WF_vars(sendMessages(self))
        /\ \A self \in Nodes : WF_vars(nodeHandler(self)) /\ WF_vars(updateStatus(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


\* Invariants
StatusInvariant == \A x \in 1..N:
                status[x] = "Committed" \/ status[x] = "Aborted" \/ status[x] = "Prepared"
                
SentReceivedInvariant == \A x \in 1..N:
                sent[x] <= NumOfMessages /\ received[x] <= NumOfMessages /\ sent[x] = received[x]
                
\* Correctness
CounterCorrectness == <>(Termination /\ (\A x \in 1..N: sent[x] = NumOfMessages /\ received[x] = NumOfMessages))

=================================
