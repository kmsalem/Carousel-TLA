------------------------------- MODULE carousel -------------------------------

(***************************************************************************)
(* This is a TLA+ specification of the Carousel protocol.                  *)
(***************************************************************************)

\* References:
\*    Hillel Wayne - Practical TLA+ (https://books.google.ca/books/about/Practical_TLA+.html)
\*    Hillel Wayne - Learn TLA (https://learntla.com)
\*    Leslie Lamport - A PlusCal User's Manual (https://lamport.azurewebsites.net/tla/p-manual.pdf)
\*    Leslie Lamport - Specifying Systems (https://lamport.azurewebsites.net/tla/book.html)

\* GitHub:
\*    belaban/pluscal (https://github.com/belaban/pluscal) - simple constructs built with TLA+ and PlusCal
\*    muratdem/PlusCal-examples (https://github.com/muratdem/PlusCal-examples) - protocol models

\* Overview:
\* A client-server model with a set of "Clients" and another set of "Nodes"
\*      with in and out message channels (implemented as unbounded queues)
\*      to transmit messages and responses between the two sets
\* There are 2 concurrent processes in this spec: 
\*   1. A client process for each Client, which nondeterministically selects a subset of 
\*      the Nodes, populates the Nodes' respective in channels with messages.
\*      In addition, the client process contains a block that processes messages/responses
\*      sent by the Nodes back to the Client: it retrieves the transaction ID of the message
\*      and check if all the Nodes targeted by that transaction ID have responded
\*   2. A receiver process for each Node, which dequeues its in channel, processes the message,
\*      updates the Node's status, and sends a response (with a status nondeterministically 
\*      determined as either Abort or Commit) back to the Node that sent the message.

\* Temporal properties and correctness invariants should be put after the "END TRANSLATION" line

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* C, N are defined in the TLC model
\* C = Number of Clients
\* N = Number of Nodes
CONSTANT C, N, IDSet
ASSUME C \in Nat /\ C > 0
ASSUME N \in Nat /\ N > 0

\* Clients and Nodes as sets
Clients == [type: {"C"}, num: 1..C]
Nodes == [type: {"N"}, num: 1..N]

\* Beginning of PlusCal algorithm
(* --algorithm progress

variable
  \* Keep track of IDs already being used and processed
  idsInUse = {},
  
  \* in and out channels implemented as mappings between Nodes/Clients to their respective queues
  channels = [n \in Nodes |-> <<>>],
  inChannels = [c \in Clients |-> <<>>],

\* receiver process 
fair process nodeHandler \in Nodes
begin
    nodeHandlerStart:
    while TRUE do
        await channels[self] /= <<>>;
        with msg = Head(channels[self]) do
            with status \in {"Committed", "Aborted"} do
                inChannels[msg.client] := Append(
                    inChannels[msg.client],
                    [id |-> msg.id, serverStatus |-> status, node |-> self, type |-> "readRsp"]);
            end with;
        end with;
        channels[self] := Tail(channels[self]); 
    end while;
end process;


\* sender process
fair process clientHandler \in Clients
variable
    expectedRemaining,
    currentMsg,
    chosenSubset,
    transactionStatus = [id \in IDSet |-> "Unused"],
    abortCurrent;
begin
  clientStart:
  while TRUE do
    await idsInUse /= IDSet;
    with id \in IDSet \ idsInUse do
        with sub \in SUBSET Nodes \ {{}} do
            currentMsg := [id |-> id, client |-> self, type |-> "readReq"];
            chosenSubset := sub;
            expectedRemaining := sub;
            idsInUse := idsInUse \cup {id};
            transactionStatus[id] := "Processing";
            abortCurrent := FALSE;
        end with;
    end with;
    
    \* Send message to every server chosen
    sendLoop:
    while chosenSubset /= {} do
        with server \in chosenSubset do
            channels[server] := Append(channels[server], currentMsg);
            chosenSubset := chosenSubset \ {server};
        end with;
    end while;
 
    receiveLoop:
    while expectedRemaining /= {} do
        await inChannels[self] /= <<>>;
        with msg = Head(inChannels[self]) do
            assert msg.id = currentMsg.id;
            assert msg.node \in expectedRemaining;
            expectedRemaining := expectedRemaining \ {msg.node};
            abortCurrent := abortCurrent \/ msg.serverStatus = "Aborted";
        end with;
        inChannels[self] := Tail(inChannels[self]);
    end while;
    
    updateStatus:
    assert currentMsg.id \in idsInUse;
    idsInUse := idsInUse \ {currentMsg.id};
    with status \in {"Aborted", IF abortCurrent THEN "Aborted" ELSE "Committed"} do
        transactionStatus[currentMsg.id] := status;
    end with;
  end while;
end process;

end algorithm *)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES idsInUse, channels, inChannels, pc, expectedRemaining, currentMsg, 
          chosenSubset, transactionStatus, abortCurrent

vars == << idsInUse, channels, inChannels, pc, expectedRemaining, currentMsg, 
           chosenSubset, transactionStatus, abortCurrent >>

ProcSet == (Nodes) \cup (Clients)

Init == (* Global variables *)
        /\ idsInUse = {}
        /\ channels = [n \in Nodes |-> <<>>]
        /\ inChannels = [c \in Clients |-> <<>>]
        (* Process clientHandler *)
        /\ expectedRemaining = [self \in Clients |-> defaultInitValue]
        /\ currentMsg = [self \in Clients |-> defaultInitValue]
        /\ chosenSubset = [self \in Clients |-> defaultInitValue]
        /\ transactionStatus = [self \in Clients |-> [id \in IDSet |-> "Unused"]]
        /\ abortCurrent = [self \in Clients |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self \in Nodes -> "nodeHandlerStart"
                                        [] self \in Clients -> "clientStart"]

nodeHandlerStart(self) == /\ pc[self] = "nodeHandlerStart"
                          /\ channels[self] /= <<>>
                          /\ LET msg == Head(channels[self]) IN
                               \E status \in {"Committed", "Aborted"}:
                                 inChannels' = [inChannels EXCEPT ![msg.client] =                       Append(
                                                                                  inChannels[msg.client],
                                                                                  [id |-> msg.id, serverStatus |-> status, node |-> self, type |-> "readRsp"])]
                          /\ channels' = [channels EXCEPT ![self] = Tail(channels[self])]
                          /\ pc' = [pc EXCEPT ![self] = "nodeHandlerStart"]
                          /\ UNCHANGED << idsInUse, expectedRemaining, 
                                          currentMsg, chosenSubset, 
                                          transactionStatus, abortCurrent >>

nodeHandler(self) == nodeHandlerStart(self)

clientStart(self) == /\ pc[self] = "clientStart"
                     /\ idsInUse /= IDSet
                     /\ \E id \in IDSet \ idsInUse:
                          \E sub \in SUBSET Nodes \ {{}}:
                            /\ currentMsg' = [currentMsg EXCEPT ![self] = [id |-> id, client |-> self, type |-> "readReq"]]
                            /\ chosenSubset' = [chosenSubset EXCEPT ![self] = sub]
                            /\ expectedRemaining' = [expectedRemaining EXCEPT ![self] = sub]
                            /\ idsInUse' = (idsInUse \cup {id})
                            /\ transactionStatus' = [transactionStatus EXCEPT ![self][id] = "Processing"]
                            /\ abortCurrent' = [abortCurrent EXCEPT ![self] = FALSE]
                     /\ pc' = [pc EXCEPT ![self] = "sendLoop"]
                     /\ UNCHANGED << channels, inChannels >>

sendLoop(self) == /\ pc[self] = "sendLoop"
                  /\ IF chosenSubset[self] /= {}
                        THEN /\ \E server \in chosenSubset[self]:
                                  /\ channels' = [channels EXCEPT ![server] = Append(channels[server], currentMsg[self])]
                                  /\ chosenSubset' = [chosenSubset EXCEPT ![self] = chosenSubset[self] \ {server}]
                             /\ pc' = [pc EXCEPT ![self] = "sendLoop"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "receiveLoop"]
                             /\ UNCHANGED << channels, chosenSubset >>
                  /\ UNCHANGED << idsInUse, inChannels, expectedRemaining, 
                                  currentMsg, transactionStatus, abortCurrent >>

receiveLoop(self) == /\ pc[self] = "receiveLoop"
                     /\ IF expectedRemaining[self] /= {}
                           THEN /\ inChannels[self] /= <<>>
                                /\ LET msg == Head(inChannels[self]) IN
                                     /\ Assert(msg.id = currentMsg[self].id, 
                                               "Failure of assertion at line 111, column 13.")
                                     /\ Assert(msg.node \in expectedRemaining[self], 
                                               "Failure of assertion at line 112, column 13.")
                                     /\ expectedRemaining' = [expectedRemaining EXCEPT ![self] = expectedRemaining[self] \ {msg.node}]
                                     /\ abortCurrent' = [abortCurrent EXCEPT ![self] = abortCurrent[self] \/ msg.serverStatus = "Aborted"]
                                /\ inChannels' = [inChannels EXCEPT ![self] = Tail(inChannels[self])]
                                /\ pc' = [pc EXCEPT ![self] = "receiveLoop"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "updateStatus"]
                                /\ UNCHANGED << inChannels, expectedRemaining, 
                                                abortCurrent >>
                     /\ UNCHANGED << idsInUse, channels, currentMsg, 
                                     chosenSubset, transactionStatus >>

updateStatus(self) == /\ pc[self] = "updateStatus"
                      /\ Assert(currentMsg[self].id \in idsInUse, 
                                "Failure of assertion at line 120, column 5.")
                      /\ idsInUse' = idsInUse \ {currentMsg[self].id}
                      /\ \E status \in {"Aborted", IF abortCurrent[self] THEN "Aborted" ELSE "Committed"}:
                           transactionStatus' = [transactionStatus EXCEPT ![self][currentMsg[self].id] = status]
                      /\ pc' = [pc EXCEPT ![self] = "clientStart"]
                      /\ UNCHANGED << channels, inChannels, expectedRemaining, 
                                      currentMsg, chosenSubset, abortCurrent >>

clientHandler(self) == clientStart(self) \/ sendLoop(self)
                          \/ receiveLoop(self) \/ updateStatus(self)

Next == (\E self \in Nodes: nodeHandler(self))
           \/ (\E self \in Clients: clientHandler(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(nodeHandler(self))
        /\ \A self \in Clients : WF_vars(clientHandler(self))

\* END TRANSLATION

\* Invariants
ProcessingInvariant == \A id \in IDSet: \A x, y \in Clients: \/ x = y
                                                             \/ transactionStatus[x][id] /= "Processing"
                                                             \/ transactionStatus[y][id] /= "Processing"
                                                             
InUseInvariant == \A id \in IDSet: (\E x \in Clients: transactionStatus[x][id] = "Processing") <=> (id \in idsInUse)

\*StatusInvariant == \A x \in 1..N:
\*                status[x] = "Committed" \/ status[x] = "Aborted" \/ status[x] = "Prepared" \/ status[x] = "Initiated"
\*                
\*SentReceivedInvariant == \A x \in 1..N:
\*                sent[x] <= NumOfMessages /\ received[x] <= NumOfMessages /\ sent[x] < received[x]
\*                
\*\* Correctness
\*CounterCorrectness == <>(Termination /\ (\A x \in 1..N: sent[x] = NumOfMessages /\ received[x] = NumOfMessages))

=================================
