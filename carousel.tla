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
end macro


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
    IncrementSent:
        sent[node] := sent[node] + 1;
    IncrementCounter:
        counter := counter + 1;
    end while;
end procedure


fair process loadChannels \in Nodes
variables
    counter = 0
begin P0: 
    with rand \in Nodes do
        call sendMessages(rand);
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
\* Label P0 of procedure sendMessages at line 73 col 5 changed to P0_
\* Label P0 of process loadChannels at line 91 col 5 changed to P0_l
\* Procedure variable incoming of procedure updateStatus at line 49 col 5 changed to incoming_
\* Procedure variable incoming of procedure updateCounter at line 61 col 5 changed to incoming_u
\* Parameter node of procedure updateStatus at line 47 col 24 changed to node_
\* Parameter node of procedure updateCounter at line 59 col 25 changed to node_u
CONSTANT defaultInitValue
VARIABLES status, sent, received, queue, channels, switchHappened, unacked, 
          pc, stack, node_, incoming_, node_u, incoming_u, node, incoming, 
          counter, message

vars == << status, sent, received, queue, channels, switchHappened, unacked, 
           pc, stack, node_, incoming_, node_u, incoming_u, node, incoming, 
           counter, message >>

ProcSet == (Nodes) \cup (Nodes)

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
        /\ incoming = [ self \in ProcSet |-> ""]
        (* Process loadChannels *)
        /\ counter = [self \in Nodes |-> 0]
        (* Process nodeHandler *)
        /\ message = [self \in Nodes |-> ""]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Nodes -> "P0_l"
                                        [] self \in Nodes -> "P0"]

P1_(self) == /\ pc[self] = "P1_"
             /\ (channels[node_[self]]) /= <<>>
             /\ incoming_' = [incoming_ EXCEPT ![self] = Head((channels[node_[self]]))]
             /\ channels' = [channels EXCEPT ![node_[self]] = Tail((channels[node_[self]]))]
             /\ pc' = [pc EXCEPT ![self] = "IncrementReceived"]
             /\ UNCHANGED << status, sent, received, queue, switchHappened, 
                             unacked, stack, node_, node_u, incoming_u, node, 
                             incoming, counter, message >>

IncrementReceived(self) == /\ pc[self] = "IncrementReceived"
                           /\ received' = [received EXCEPT ![node_[self]] = received[node_[self]] + 1]
                           /\ pc' = [pc EXCEPT ![self] = "Update"]
                           /\ UNCHANGED << status, sent, queue, channels, 
                                           switchHappened, unacked, stack, 
                                           node_, incoming_, node_u, 
                                           incoming_u, node, incoming, counter, 
                                           message >>

Update(self) == /\ pc[self] = "Update"
                /\ status' = [status EXCEPT ![node_[self]] = incoming_[self]]
                /\ pc' = [pc EXCEPT ![self] = "Error"]
                /\ UNCHANGED << sent, received, queue, channels, 
                                switchHappened, unacked, stack, node_, 
                                incoming_, node_u, incoming_u, node, incoming, 
                                counter, message >>

updateStatus(self) == P1_(self) \/ IncrementReceived(self) \/ Update(self)

P1(self) == /\ pc[self] = "P1"
            /\ (channels[node_u[self]]) /= <<>>
            /\ incoming_u' = [incoming_u EXCEPT ![self] = Head((channels[node_u[self]]))]
            /\ channels' = [channels EXCEPT ![node_u[self]] = Tail((channels[node_u[self]]))]
            /\ status' = [status EXCEPT ![node_u[self]] = incoming_u'[self]]
            /\ pc' = [pc EXCEPT ![self] = "Error"]
            /\ UNCHANGED << sent, received, queue, switchHappened, unacked, 
                            stack, node_, incoming_, node_u, node, incoming, 
                            counter, message >>

updateCounter(self) == P1(self)

P0_(self) == /\ pc[self] = "P0_"
             /\ IF counter[self] < NumOfMessages
                   THEN /\ pc' = [pc EXCEPT ![self] = "Send"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "Error"]
             /\ UNCHANGED << status, sent, received, queue, channels, 
                             switchHappened, unacked, stack, node_, incoming_, 
                             node_u, incoming_u, node, incoming, counter, 
                             message >>

Send(self) == /\ pc[self] = "Send"
              /\ \/ /\ channels' = [channels EXCEPT ![node[self]] = Append((channels[node[self]]), "Committed")]
                 \/ /\ channels' = [channels EXCEPT ![node[self]] = Append((channels[node[self]]), "Aborted")]
                 \/ /\ channels' = [channels EXCEPT ![node[self]] = Append((channels[node[self]]), "Prepared")]
              /\ pc' = [pc EXCEPT ![self] = "IncrementSent"]
              /\ UNCHANGED << status, sent, received, queue, switchHappened, 
                              unacked, stack, node_, incoming_, node_u, 
                              incoming_u, node, incoming, counter, message >>

IncrementSent(self) == /\ pc[self] = "IncrementSent"
                       /\ sent' = [sent EXCEPT ![node[self]] = sent[node[self]] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "IncrementCounter"]
                       /\ UNCHANGED << status, received, queue, channels, 
                                       switchHappened, unacked, stack, node_, 
                                       incoming_, node_u, incoming_u, node, 
                                       incoming, counter, message >>

IncrementCounter(self) == /\ pc[self] = "IncrementCounter"
                          /\ counter' = [counter EXCEPT ![self] = counter[self] + 1]
                          /\ pc' = [pc EXCEPT ![self] = "P0_"]
                          /\ UNCHANGED << status, sent, received, queue, 
                                          channels, switchHappened, unacked, 
                                          stack, node_, incoming_, node_u, 
                                          incoming_u, node, incoming, message >>

sendMessages(self) == P0_(self) \/ Send(self) \/ IncrementSent(self)
                         \/ IncrementCounter(self)

P0_l(self) == /\ pc[self] = "P0_l"
              /\ \E rand \in Nodes:
                   /\ /\ node' = [node EXCEPT ![self] = rand]
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "sendMessages",
                                                               pc        |->  "Done",
                                                               incoming  |->  incoming[self],
                                                               node      |->  node[self] ] >>
                                                           \o stack[self]]
                   /\ incoming' = [incoming EXCEPT ![self] = ""]
                   /\ pc' = [pc EXCEPT ![self] = "P0_"]
              /\ UNCHANGED << status, sent, received, queue, channels, 
                              switchHappened, unacked, node_, incoming_, 
                              node_u, incoming_u, counter, message >>

loadChannels(self) == P0_l(self)

P0(self) == /\ pc[self] = "P0"
            /\ IF channels[self] # <<>>
                  THEN /\ pc' = [pc EXCEPT ![self] = "Write"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << status, sent, received, queue, channels, 
                            switchHappened, unacked, stack, node_, incoming_, 
                            node_u, incoming_u, node, incoming, counter, 
                            message >>

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
                               node, incoming, counter, message >>

nodeHandler(self) == P0(self) \/ Write(self)

Next == (\E self \in ProcSet:  \/ updateStatus(self) \/ updateCounter(self)
                               \/ sendMessages(self))
           \/ (\E self \in Nodes: loadChannels(self))
           \/ (\E self \in Nodes: nodeHandler(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(loadChannels(self)) /\ WF_vars(sendMessages(self))
        /\ \A self \in Nodes : WF_vars(nodeHandler(self)) /\ WF_vars(updateStatus(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* Invariants
StatusInvariant == \A x \in 1..N:
                status[x] = "Committed" \/ status[x] = "Initiated"
                
SentReceivedInvariant == \A x \in 1..N:
                sent[x] <= NumOfMessages /\ received[x] <= NumOfMessages /\ sent[x] = received[x]
                
\* Correctness
CounterCorrectness == <>(Termination /\ (\A x \in 1..N: sent[x] = NumOfMessages /\ received[x] = NumOfMessages))

=================================
