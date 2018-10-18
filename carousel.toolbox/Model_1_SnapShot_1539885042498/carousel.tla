------------------------------- MODULE carousel -------------------------------

(***************************************************************************)
(* This is a TLA+ specification of the Carousel protocol.                  *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets, Sequences, TLC
CONSTANT N, NumOfMessages
ASSUME N \in Nat /\ N > 0
Nodes == 1..N

(* --algorithm progress
variable
  \* Status of each node
  status = [n \in Nodes |-> "Initiated"],
  counters = [n \in Nodes |-> 0],
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


fair process loadChannels \in Nodes
variable
    counter = 0;
begin P0:
    while counter < NumOfMessages do
        send(channels[self], "Committed");
        counter := counter + 1;
\*        send(channels[self], counter);
    end while;
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
\* Label P1 of procedure updateStatus at line 29 col 3 changed to P1_
\* Label P0 of process loadChannels at line 64 col 5 changed to P0_
\* Procedure variable incoming of procedure updateStatus at line 43 col 5 changed to incoming_
\* Parameter node of procedure updateStatus at line 41 col 24 changed to node_
CONSTANT defaultInitValue
VARIABLES status, counters, queue, channels, switchHappened, unacked, pc, 
          stack, node_, incoming_, node, incoming, counter, message

vars == << status, counters, queue, channels, switchHappened, unacked, pc, 
           stack, node_, incoming_, node, incoming, counter, message >>

ProcSet == (Nodes) \cup (Nodes)

Init == (* Global variables *)
        /\ status = [n \in Nodes |-> "Initiated"]
        /\ counters = [n \in Nodes |-> 0]
        /\ queue = <<>>
        /\ channels = [n \in Nodes |-> <<>>]
        /\ switchHappened = 0
        /\ unacked = 0
        (* Procedure updateStatus *)
        /\ node_ = [ self \in ProcSet |-> defaultInitValue]
        /\ incoming_ = [ self \in ProcSet |-> ""]
        (* Procedure updateCounter *)
        /\ node = [ self \in ProcSet |-> defaultInitValue]
        /\ incoming = [ self \in ProcSet |-> ""]
        (* Process loadChannels *)
        /\ counter = [self \in Nodes |-> 0]
        (* Process nodeHandler *)
        /\ message = [self \in Nodes |-> ""]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Nodes -> "P0_"
                                        [] self \in Nodes -> "P0"]

P1_(self) == /\ pc[self] = "P1_"
             /\ (channels[node_[self]]) /= <<>>
             /\ incoming_' = [incoming_ EXCEPT ![self] = Head((channels[node_[self]]))]
             /\ channels' = [channels EXCEPT ![node_[self]] = Tail((channels[node_[self]]))]
             /\ status' = [status EXCEPT ![node_[self]] = incoming_'[self]]
             /\ pc' = [pc EXCEPT ![self] = "Error"]
             /\ UNCHANGED << counters, queue, switchHappened, unacked, stack, 
                             node_, node, incoming, counter, message >>

updateStatus(self) == P1_(self)

P1(self) == /\ pc[self] = "P1"
            /\ (channels[node[self]]) /= <<>>
            /\ incoming' = [incoming EXCEPT ![self] = Head((channels[node[self]]))]
            /\ channels' = [channels EXCEPT ![node[self]] = Tail((channels[node[self]]))]
            /\ counters' = [counters EXCEPT ![node[self]] = incoming'[self]]
            /\ pc' = [pc EXCEPT ![self] = "Error"]
            /\ UNCHANGED << status, queue, switchHappened, unacked, stack, 
                            node_, incoming_, node, counter, message >>

updateCounter(self) == P1(self)

P0_(self) == /\ pc[self] = "P0_"
             /\ IF counter[self] < NumOfMessages
                   THEN /\ channels' = [channels EXCEPT ![self] = Append((channels[self]), "Committed")]
                        /\ counter' = [counter EXCEPT ![self] = counter[self] + 1]
                        /\ pc' = [pc EXCEPT ![self] = "P0_"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << channels, counter >>
             /\ UNCHANGED << status, counters, queue, switchHappened, unacked, 
                             stack, node_, incoming_, node, incoming, message >>

loadChannels(self) == P0_(self)

P0(self) == /\ pc[self] = "P0"
            /\ IF channels[self] # <<>>
                  THEN /\ pc' = [pc EXCEPT ![self] = "Write"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << status, counters, queue, channels, switchHappened, 
                            unacked, stack, node_, incoming_, node, incoming, 
                            counter, message >>

Write(self) == /\ pc[self] = "Write"
               /\ /\ node_' = [node_ EXCEPT ![self] = self]
                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "updateStatus",
                                                           pc        |->  "P0",
                                                           incoming_ |->  incoming_[self],
                                                           node_     |->  node_[self] ] >>
                                                       \o stack[self]]
               /\ incoming_' = [incoming_ EXCEPT ![self] = ""]
               /\ pc' = [pc EXCEPT ![self] = "P1_"]
               /\ UNCHANGED << status, counters, queue, channels, 
                               switchHappened, unacked, node, incoming, 
                               counter, message >>

nodeHandler(self) == P0(self) \/ Write(self)

Next == (\E self \in ProcSet: updateStatus(self) \/ updateCounter(self))
           \/ (\E self \in Nodes: loadChannels(self))
           \/ (\E self \in Nodes: nodeHandler(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(loadChannels(self))
        /\ \A self \in Nodes : WF_vars(nodeHandler(self)) /\ WF_vars(updateStatus(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* Invariants
StatusInvariant == \A x \in 1..N:
                status[x] = "Committeda" \/ status[x] = "Initiated"
                
\* Correctness
CounterCorrectness == <>(Termination /\ (\A x \in 1..N: counters[x] = NumOfMessages))

=================================
