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


fair process loadChannels \in Nodes
variable
    counter = 0;
begin P0:
    while counter < NumOfMessages do
        send(channels[self], "Committed");
        counter := counter + 1;
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
\* Label P0 of process loadChannels at line 54 col 5 changed to P0_
CONSTANT defaultInitValue
VARIABLES status, queue, channels, switchHappened, unacked, pc, stack, node, 
          incoming, counter, message

vars == << status, queue, channels, switchHappened, unacked, pc, stack, node, 
           incoming, counter, message >>

ProcSet == (Nodes) \cup (Nodes)

Init == (* Global variables *)
        /\ status = [n \in Nodes |-> "Initiated"]
        /\ queue = <<>>
        /\ channels = [n \in Nodes |-> <<>>]
        /\ switchHappened = 0
        /\ unacked = 0
        (* Procedure updateStatus *)
        /\ node = [ self \in ProcSet |-> defaultInitValue]
        /\ incoming = [ self \in ProcSet |-> ""]
        (* Process loadChannels *)
        /\ counter = [self \in Nodes |-> 0]
        (* Process nodeHandler *)
        /\ message = [self \in Nodes |-> ""]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Nodes -> "P0_"
                                        [] self \in Nodes -> "P0"]

P1(self) == /\ pc[self] = "P1"
            /\ (channels[node[self]]) /= <<>>
            /\ incoming' = [incoming EXCEPT ![self] = Head((channels[node[self]]))]
            /\ channels' = [channels EXCEPT ![node[self]] = Tail((channels[node[self]]))]
            /\ status' = [status EXCEPT ![node[self]] = incoming'[self]]
            /\ pc' = [pc EXCEPT ![self] = "Error"]
            /\ UNCHANGED << queue, switchHappened, unacked, stack, node, 
                            counter, message >>

updateStatus(self) == P1(self)

P0_(self) == /\ pc[self] = "P0_"
             /\ IF counter[self] < NumOfMessages
                   THEN /\ channels' = [channels EXCEPT ![self] = Append((channels[self]), "Committed")]
                        /\ counter' = [counter EXCEPT ![self] = counter[self] + 1]
                        /\ pc' = [pc EXCEPT ![self] = "P0_"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << channels, counter >>
             /\ UNCHANGED << status, queue, switchHappened, unacked, stack, 
                             node, incoming, message >>

loadChannels(self) == P0_(self)

P0(self) == /\ pc[self] = "P0"
            /\ IF channels[self] # <<>>
                  THEN /\ pc' = [pc EXCEPT ![self] = "Write"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << status, queue, channels, switchHappened, unacked, 
                            stack, node, incoming, counter, message >>

Write(self) == /\ pc[self] = "Write"
               /\ /\ node' = [node EXCEPT ![self] = self]
                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "updateStatus",
                                                           pc        |->  "P0",
                                                           incoming  |->  incoming[self],
                                                           node      |->  node[self] ] >>
                                                       \o stack[self]]
               /\ incoming' = [incoming EXCEPT ![self] = ""]
               /\ pc' = [pc EXCEPT ![self] = "P1"]
               /\ UNCHANGED << status, queue, channels, switchHappened, 
                               unacked, counter, message >>

nodeHandler(self) == P0(self) \/ Write(self)

Next == (\E self \in ProcSet: updateStatus(self))
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
Correctness == <>(\A x \in status: x = "Committed")

=================================
