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

EXTENDS Naturals, FiniteSets, Sequences, TLC, Bags

\* Defined in the model
\* C = Number of Clients
\* N = Number of Nodes
\* M = Number of Coordinators
\* IDSet = Set of labels
CONSTANT C, N, M, IDSet, ClientQSize, NodeQSize, CoordQSize
ASSUME C \in Nat /\ C > 0
ASSUME N \in Nat /\ N > 0
ASSUME M \in Nat /\ M > 0
ASSUME ClientQSize \in Nat /\ ClientQSize > 0
ASSUME NodeQSize \in Nat /\ NodeQSize > 0
ASSUME CoordQSize \in Nat /\ CoordQSize > 0

\* Clients and Nodes as sets
Clients == [type: {"Client"}, num: 1..C]
Nodes == [type: {"Node"}, num: 1..N]
Coords == [type: {"Coord"}, num: 1..M]
DummyRecord == [type |-> "dummy"]

\* Beginning of PlusCal algorithm
(* --algorithm progress

variables
    \* Each process has its view of the status of a transaction
    transactionStatus = [x \in Clients \cup Nodes \cup Coords |-> [id \in IDSet |-> "Init"]],
    \* Information for each transaction, used by coordinators
    \* A coordinator should only read from an entry if it is processing that transaction
    transactionInfo = [id \in IDSet |-> DummyRecord],
    serverResponses = [id \in IDSet |-> EmptyBag],
    clientDecisions = [id \in IDSet |-> "Init"],
    \* Each process has a queue of messages to process
    channels = [x \in Clients \cup Nodes \cup Coords |-> <<>>];

\* A transaction ID is free iff a process is not currently processing it  
define
    idsInUse == {id \in IDSet : (\E x \in Clients \cup Nodes \cup Coords :
                                 transactionStatus[x][id] = "Processing")}
    minProc(procs) == CHOOSE p \in procs : \A q \in procs : p.num <= q.num
end define;

macro send(msg, proc)
begin
    await Len(channels[proc]) < CASE proc \in Clients -> ClientQSize
                                  [] proc \in Nodes -> NodeQSize
                                  [] proc \in Coords -> CoordQSize;
    channels[proc] := Append(channels[proc], msg);
end macro;

\* receiver process 
fair process nodeHandler \in Nodes
variable
    currentMsg;
begin
nodeHandlerStart:
while TRUE do
    await channels[self] /= <<>>;
    with msg = Head(channels[self]) do
        currentMsg := msg;
    end with;
    channels[self] := Tail(channels[self]);
     
    nodeProcessMsg:
    if currentMsg.type = "readReq" then
        transactionStatus[self][currentMsg.id] := "Processing";
        send([id |-> currentMsg.id, node |-> self, type |-> "readRsp"], currentMsg.client);
        
        nodeToCoord:
        with prepareResult \in {"Prepared", "Aborted"} do
            send([id |-> currentMsg.id, node |-> self, type |-> "prepareRsp", result |-> prepareResult], currentMsg.coord);
        end with;
     else
        assert currentMsg.type = "commitToNode";
        assert transactionStatus[self][currentMsg.id] = "Processing";
        transactionStatus[self][currentMsg.id] := currentMsg.decision;
     end if;
end while;
end process;

\* coordinator process
\* Makes final decision about whether a transaction is committed
\* Note that we do not implement the full 2PC algorithm
fair process coordHandler \in Coords
variable
    currentMsg,
    commitDecision,
    remainingServers;
begin
coordHandlerStart:
while TRUE do
    await channels[self] /= <<>>;
    with msg = Head(channels[self]) do
        currentMsg := msg;
    end with;
    channels[self] := Tail(channels[self]);
    
    coordProcessMsg:
    if currentMsg.type = "txnInfo" then
        transactionStatus[self][currentMsg.id] := "Processing";
        transactionInfo[currentMsg.id] := currentMsg;    
    elsif currentMsg.type = "prepareRsp" then
        transactionStatus[self][currentMsg.id] := "Processing";
        serverResponses[currentMsg.id] := serverResponses[currentMsg.id] (+) SetToBag({currentMsg.result});
    else
        transactionStatus[self][currentMsg.id] := "Processing";
        clientDecisions[currentMsg.id] := currentMsg.decision;
    end if;
    
    checkForDecision:
    assert transactionStatus[self][currentMsg.id] = "Processing";
    if /\ transactionInfo[currentMsg.id] /= DummyRecord
       /\ BagCardinality(serverResponses[currentMsg.id]) = Cardinality(transactionInfo[currentMsg.id].servers)
       /\ clientDecisions[currentMsg.id] /= "Init" then
        commitDecision := IF /\ BagToSet(serverResponses[currentMsg.id]) = {"Prepared"}
                             /\ clientDecisions[currentMsg.id] = "Commit"
                          THEN "Committed" ELSE "Aborted";
        remainingServers := transactionInfo[currentMsg.id].servers;
        
        sendDecisionToClient:
        with client = transactionInfo[currentMsg.id].client do
            send([id |-> currentMsg.id, type |-> "commitDecision", decision |-> commitDecision], client);
        end with;
        
        sendDecisionToNodes:
        while remainingServers /= {} do
            with server = minProc(remainingServers) do
                send([id |-> currentMsg.id, type |-> "commitToNode", decision |-> commitDecision], server);
                remainingServers := remainingServers \ {server};
            end with;
        end while;
        
        updateCoordStatus:
        transactionStatus[self][currentMsg.id] := commitDecision;
        serverResponses[currentMsg.id] := EmptyBag;
        clientDecisions[currentMsg.id] := "Init";
        transactionInfo[currentMsg.id] := DummyRecord;
    end if;
end while;
end process;


\* sender process
\* Processes only one transaction at a time
fair process clientHandler \in Clients
variable
    remainingServers,
    currentMsg,
    chosenServers,
begin
clientStart:
while TRUE do
    await idsInUse /= IDSet;
    with id \in IDSet \ idsInUse, sub \in SUBSET Nodes \ {{}}, coord \in Coords do
        currentMsg := [id |-> id, client |-> self, type |-> "readReq", coord |-> coord];
        chosenServers := sub;
        remainingServers := sub;
        transactionStatus[self][id] := "Processing";
    end with;

    \* Send message to every server chosen
    sendLoop:
    while remainingServers /= {} do
        with server = minProc(remainingServers) do
            send(currentMsg, server);
            remainingServers := remainingServers \ {server};
        end with;
    end while;
    
    sendInfoToCoord:
    send([id |-> currentMsg.id, client |-> self, type |-> "txnInfo", servers |-> chosenServers], currentMsg.coord);
    remainingServers := chosenServers;
    
    receiveLoop:
    while remainingServers /= {} do
        await channels[self] /= <<>>;
        with msg = Head(channels[self]) do
            assert msg.id = currentMsg.id;
            assert msg.node \in remainingServers;
            assert msg.type = "readRsp";
            remainingServers := remainingServers \ {msg.node};
        end with;
        channels[self] := Tail(channels[self]);
    end while;
    
    sendDecision:
    with decision \in {"Abort", "Commit"} do
        send([id |-> currentMsg.id, client |-> self, type |-> "commitReq", decision |-> decision], currentMsg.coord);
    end with;
    
    getFinalDecision:
    await channels[self] /= <<>>;
    with msg = Head(channels[self]) do
        assert msg.id = currentMsg.id;
        assert msg.type = "commitDecision";
        transactionStatus[self][currentMsg.id] := msg.decision;
    end with;
    channels[self] := Tail(channels[self]);
end while;
end process;

end algorithm *)
\* BEGIN TRANSLATION
\* Process variable currentMsg of process nodeHandler at line 86 col 5 changed to currentMsg_
\* Process variable currentMsg of process coordHandler at line 118 col 5 changed to currentMsg_c
\* Process variable remainingServers of process coordHandler at line 120 col 5 changed to remainingServers_
CONSTANT defaultInitValue
VARIABLES transactionStatus, transactionInfo, serverResponses, 
          clientDecisions, channels, pc

(* define statement *)
idsInUse == {id \in IDSet : (\E x \in Clients \cup Nodes \cup Coords :
                             transactionStatus[x][id] = "Processing")}
minProc(procs) == CHOOSE p \in procs : \A q \in procs : p.num <= q.num

VARIABLES currentMsg_, currentMsg_c, commitDecision, remainingServers_, 
          remainingServers, currentMsg, chosenServers

vars == << transactionStatus, transactionInfo, serverResponses, 
           clientDecisions, channels, pc, currentMsg_, currentMsg_c, 
           commitDecision, remainingServers_, remainingServers, currentMsg, 
           chosenServers >>

ProcSet == (Nodes) \cup (Coords) \cup (Clients)

Init == (* Global variables *)
        /\ transactionStatus = [x \in Clients \cup Nodes \cup Coords |-> [id \in IDSet |-> "Init"]]
        /\ transactionInfo = [id \in IDSet |-> DummyRecord]
        /\ serverResponses = [id \in IDSet |-> EmptyBag]
        /\ clientDecisions = [id \in IDSet |-> "Init"]
        /\ channels = [x \in Clients \cup Nodes \cup Coords |-> <<>>]
        (* Process nodeHandler *)
        /\ currentMsg_ = [self \in Nodes |-> defaultInitValue]
        (* Process coordHandler *)
        /\ currentMsg_c = [self \in Coords |-> defaultInitValue]
        /\ commitDecision = [self \in Coords |-> defaultInitValue]
        /\ remainingServers_ = [self \in Coords |-> defaultInitValue]
        (* Process clientHandler *)
        /\ remainingServers = [self \in Clients |-> defaultInitValue]
        /\ currentMsg = [self \in Clients |-> defaultInitValue]
        /\ chosenServers = [self \in Clients |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self \in Nodes -> "nodeHandlerStart"
                                        [] self \in Coords -> "coordHandlerStart"
                                        [] self \in Clients -> "clientStart"]

nodeHandlerStart(self) == /\ pc[self] = "nodeHandlerStart"
                          /\ channels[self] /= <<>>
                          /\ LET msg == Head(channels[self]) IN
                               currentMsg_' = [currentMsg_ EXCEPT ![self] = msg]
                          /\ channels' = [channels EXCEPT ![self] = Tail(channels[self])]
                          /\ pc' = [pc EXCEPT ![self] = "nodeProcessMsg"]
                          /\ UNCHANGED << transactionStatus, transactionInfo, 
                                          serverResponses, clientDecisions, 
                                          currentMsg_c, commitDecision, 
                                          remainingServers_, remainingServers, 
                                          currentMsg, chosenServers >>

nodeProcessMsg(self) == /\ pc[self] = "nodeProcessMsg"
                        /\ IF currentMsg_[self].type = "readReq"
                              THEN /\ transactionStatus' = [transactionStatus EXCEPT ![self][currentMsg_[self].id] = "Processing"]
                                   /\ Len(channels[(currentMsg_[self].client)]) < CASE (currentMsg_[self].client) \in Clients -> ClientQSize
                                                                                    [] (currentMsg_[self].client) \in Nodes -> NodeQSize
                                                                                    [] (currentMsg_[self].client) \in Coords -> CoordQSize
                                   /\ channels' = [channels EXCEPT ![(currentMsg_[self].client)] = Append(channels[(currentMsg_[self].client)], ([id |-> currentMsg_[self].id, node |-> self, type |-> "readRsp"]))]
                                   /\ pc' = [pc EXCEPT ![self] = "nodeToCoord"]
                              ELSE /\ Assert(currentMsg_[self].type = "commitToNode", 
                                             "Failure of assertion at line 106, column 9.")
                                   /\ Assert(transactionStatus[self][currentMsg_[self].id] = "Processing", 
                                             "Failure of assertion at line 107, column 9.")
                                   /\ transactionStatus' = [transactionStatus EXCEPT ![self][currentMsg_[self].id] = currentMsg_[self].decision]
                                   /\ pc' = [pc EXCEPT ![self] = "nodeHandlerStart"]
                                   /\ UNCHANGED channels
                        /\ UNCHANGED << transactionInfo, serverResponses, 
                                        clientDecisions, currentMsg_, 
                                        currentMsg_c, commitDecision, 
                                        remainingServers_, remainingServers, 
                                        currentMsg, chosenServers >>

nodeToCoord(self) == /\ pc[self] = "nodeToCoord"
                     /\ \E prepareResult \in {"Prepared", "Aborted"}:
                          /\ Len(channels[(currentMsg_[self].coord)]) < CASE (currentMsg_[self].coord) \in Clients -> ClientQSize
                                                                          [] (currentMsg_[self].coord) \in Nodes -> NodeQSize
                                                                          [] (currentMsg_[self].coord) \in Coords -> CoordQSize
                          /\ channels' = [channels EXCEPT ![(currentMsg_[self].coord)] = Append(channels[(currentMsg_[self].coord)], ([id |-> currentMsg_[self].id, node |-> self, type |-> "prepareRsp", result |-> prepareResult]))]
                     /\ pc' = [pc EXCEPT ![self] = "nodeHandlerStart"]
                     /\ UNCHANGED << transactionStatus, transactionInfo, 
                                     serverResponses, clientDecisions, 
                                     currentMsg_, currentMsg_c, commitDecision, 
                                     remainingServers_, remainingServers, 
                                     currentMsg, chosenServers >>

nodeHandler(self) == nodeHandlerStart(self) \/ nodeProcessMsg(self)
                        \/ nodeToCoord(self)

coordHandlerStart(self) == /\ pc[self] = "coordHandlerStart"
                           /\ channels[self] /= <<>>
                           /\ LET msg == Head(channels[self]) IN
                                currentMsg_c' = [currentMsg_c EXCEPT ![self] = msg]
                           /\ channels' = [channels EXCEPT ![self] = Tail(channels[self])]
                           /\ pc' = [pc EXCEPT ![self] = "coordProcessMsg"]
                           /\ UNCHANGED << transactionStatus, transactionInfo, 
                                           serverResponses, clientDecisions, 
                                           currentMsg_, commitDecision, 
                                           remainingServers_, remainingServers, 
                                           currentMsg, chosenServers >>

coordProcessMsg(self) == /\ pc[self] = "coordProcessMsg"
                         /\ IF currentMsg_c[self].type = "txnInfo"
                               THEN /\ transactionStatus' = [transactionStatus EXCEPT ![self][currentMsg_c[self].id] = "Processing"]
                                    /\ transactionInfo' = [transactionInfo EXCEPT ![currentMsg_c[self].id] = currentMsg_c[self]]
                                    /\ UNCHANGED << serverResponses, 
                                                    clientDecisions >>
                               ELSE /\ IF currentMsg_c[self].type = "prepareRsp"
                                          THEN /\ transactionStatus' = [transactionStatus EXCEPT ![self][currentMsg_c[self].id] = "Processing"]
                                               /\ serverResponses' = [serverResponses EXCEPT ![currentMsg_c[self].id] = serverResponses[currentMsg_c[self].id] (+) SetToBag({currentMsg_c[self].result})]
                                               /\ UNCHANGED clientDecisions
                                          ELSE /\ transactionStatus' = [transactionStatus EXCEPT ![self][currentMsg_c[self].id] = "Processing"]
                                               /\ clientDecisions' = [clientDecisions EXCEPT ![currentMsg_c[self].id] = currentMsg_c[self].decision]
                                               /\ UNCHANGED serverResponses
                                    /\ UNCHANGED transactionInfo
                         /\ pc' = [pc EXCEPT ![self] = "checkForDecision"]
                         /\ UNCHANGED << channels, currentMsg_, currentMsg_c, 
                                         commitDecision, remainingServers_, 
                                         remainingServers, currentMsg, 
                                         chosenServers >>

checkForDecision(self) == /\ pc[self] = "checkForDecision"
                          /\ Assert(transactionStatus[self][currentMsg_c[self].id] = "Processing", 
                                    "Failure of assertion at line 143, column 5.")
                          /\ IF /\ transactionInfo[currentMsg_c[self].id] /= DummyRecord
                                /\ BagCardinality(serverResponses[currentMsg_c[self].id]) = Cardinality(transactionInfo[currentMsg_c[self].id].servers)
                                /\ clientDecisions[currentMsg_c[self].id] /= "Init"
                                THEN /\ commitDecision' = [commitDecision EXCEPT ![self] = IF /\ BagToSet(serverResponses[currentMsg_c[self].id]) = {"Prepared"}
                                                                                              /\ clientDecisions[currentMsg_c[self].id] = "Commit"
                                                                                           THEN "Committed" ELSE "Aborted"]
                                     /\ remainingServers_' = [remainingServers_ EXCEPT ![self] = transactionInfo[currentMsg_c[self].id].servers]
                                     /\ pc' = [pc EXCEPT ![self] = "sendDecisionToClient"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "coordHandlerStart"]
                                     /\ UNCHANGED << commitDecision, 
                                                     remainingServers_ >>
                          /\ UNCHANGED << transactionStatus, transactionInfo, 
                                          serverResponses, clientDecisions, 
                                          channels, currentMsg_, currentMsg_c, 
                                          remainingServers, currentMsg, 
                                          chosenServers >>

sendDecisionToClient(self) == /\ pc[self] = "sendDecisionToClient"
                              /\ LET client == transactionInfo[currentMsg_c[self].id].client IN
                                   /\ Len(channels[client]) < CASE client \in Clients -> ClientQSize
                                                                [] client \in Nodes -> NodeQSize
                                                                [] client \in Coords -> CoordQSize
                                   /\ channels' = [channels EXCEPT ![client] = Append(channels[client], ([id |-> currentMsg_c[self].id, type |-> "commitDecision", decision |-> commitDecision[self]]))]
                              /\ pc' = [pc EXCEPT ![self] = "sendDecisionToNodes"]
                              /\ UNCHANGED << transactionStatus, 
                                              transactionInfo, serverResponses, 
                                              clientDecisions, currentMsg_, 
                                              currentMsg_c, commitDecision, 
                                              remainingServers_, 
                                              remainingServers, currentMsg, 
                                              chosenServers >>

sendDecisionToNodes(self) == /\ pc[self] = "sendDecisionToNodes"
                             /\ IF remainingServers_[self] /= {}
                                   THEN /\ LET server == minProc(remainingServers_[self]) IN
                                             /\ Len(channels[server]) < CASE server \in Clients -> ClientQSize
                                                                          [] server \in Nodes -> NodeQSize
                                                                          [] server \in Coords -> CoordQSize
                                             /\ channels' = [channels EXCEPT ![server] = Append(channels[server], ([id |-> currentMsg_c[self].id, type |-> "commitToNode", decision |-> commitDecision[self]]))]
                                             /\ remainingServers_' = [remainingServers_ EXCEPT ![self] = remainingServers_[self] \ {server}]
                                        /\ pc' = [pc EXCEPT ![self] = "sendDecisionToNodes"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "updateCoordStatus"]
                                        /\ UNCHANGED << channels, 
                                                        remainingServers_ >>
                             /\ UNCHANGED << transactionStatus, 
                                             transactionInfo, serverResponses, 
                                             clientDecisions, currentMsg_, 
                                             currentMsg_c, commitDecision, 
                                             remainingServers, currentMsg, 
                                             chosenServers >>

updateCoordStatus(self) == /\ pc[self] = "updateCoordStatus"
                           /\ transactionStatus' = [transactionStatus EXCEPT ![self][currentMsg_c[self].id] = commitDecision[self]]
                           /\ serverResponses' = [serverResponses EXCEPT ![currentMsg_c[self].id] = EmptyBag]
                           /\ clientDecisions' = [clientDecisions EXCEPT ![currentMsg_c[self].id] = "Init"]
                           /\ transactionInfo' = [transactionInfo EXCEPT ![currentMsg_c[self].id] = DummyRecord]
                           /\ pc' = [pc EXCEPT ![self] = "coordHandlerStart"]
                           /\ UNCHANGED << channels, currentMsg_, currentMsg_c, 
                                           commitDecision, remainingServers_, 
                                           remainingServers, currentMsg, 
                                           chosenServers >>

coordHandler(self) == coordHandlerStart(self) \/ coordProcessMsg(self)
                         \/ checkForDecision(self)
                         \/ sendDecisionToClient(self)
                         \/ sendDecisionToNodes(self)
                         \/ updateCoordStatus(self)

clientStart(self) == /\ pc[self] = "clientStart"
                     /\ idsInUse /= IDSet
                     /\ \E id \in IDSet \ idsInUse:
                          \E sub \in SUBSET Nodes \ {{}}:
                            \E coord \in Coords:
                              /\ currentMsg' = [currentMsg EXCEPT ![self] = [id |-> id, client |-> self, type |-> "readReq", coord |-> coord]]
                              /\ chosenServers' = [chosenServers EXCEPT ![self] = sub]
                              /\ remainingServers' = [remainingServers EXCEPT ![self] = sub]
                              /\ transactionStatus' = [transactionStatus EXCEPT ![self][id] = "Processing"]
                     /\ pc' = [pc EXCEPT ![self] = "sendLoop"]
                     /\ UNCHANGED << transactionInfo, serverResponses, 
                                     clientDecisions, channels, currentMsg_, 
                                     currentMsg_c, commitDecision, 
                                     remainingServers_ >>

sendLoop(self) == /\ pc[self] = "sendLoop"
                  /\ IF remainingServers[self] /= {}
                        THEN /\ LET server == minProc(remainingServers[self]) IN
                                  /\ Len(channels[server]) < CASE server \in Clients -> ClientQSize
                                                               [] server \in Nodes -> NodeQSize
                                                               [] server \in Coords -> CoordQSize
                                  /\ channels' = [channels EXCEPT ![server] = Append(channels[server], currentMsg[self])]
                                  /\ remainingServers' = [remainingServers EXCEPT ![self] = remainingServers[self] \ {server}]
                             /\ pc' = [pc EXCEPT ![self] = "sendLoop"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "sendInfoToCoord"]
                             /\ UNCHANGED << channels, remainingServers >>
                  /\ UNCHANGED << transactionStatus, transactionInfo, 
                                  serverResponses, clientDecisions, 
                                  currentMsg_, currentMsg_c, commitDecision, 
                                  remainingServers_, currentMsg, chosenServers >>

sendInfoToCoord(self) == /\ pc[self] = "sendInfoToCoord"
                         /\ Len(channels[(currentMsg[self].coord)]) < CASE (currentMsg[self].coord) \in Clients -> ClientQSize
                                                                        [] (currentMsg[self].coord) \in Nodes -> NodeQSize
                                                                        [] (currentMsg[self].coord) \in Coords -> CoordQSize
                         /\ channels' = [channels EXCEPT ![(currentMsg[self].coord)] = Append(channels[(currentMsg[self].coord)], ([id |-> currentMsg[self].id, client |-> self, type |-> "txnInfo", servers |-> chosenServers[self]]))]
                         /\ remainingServers' = [remainingServers EXCEPT ![self] = chosenServers[self]]
                         /\ pc' = [pc EXCEPT ![self] = "receiveLoop"]
                         /\ UNCHANGED << transactionStatus, transactionInfo, 
                                         serverResponses, clientDecisions, 
                                         currentMsg_, currentMsg_c, 
                                         commitDecision, remainingServers_, 
                                         currentMsg, chosenServers >>

receiveLoop(self) == /\ pc[self] = "receiveLoop"
                     /\ IF remainingServers[self] /= {}
                           THEN /\ channels[self] /= <<>>
                                /\ LET msg == Head(channels[self]) IN
                                     /\ Assert(msg.id = currentMsg[self].id, 
                                               "Failure of assertion at line 210, column 13.")
                                     /\ Assert(msg.node \in remainingServers[self], 
                                               "Failure of assertion at line 211, column 13.")
                                     /\ Assert(msg.type = "readRsp", 
                                               "Failure of assertion at line 212, column 13.")
                                     /\ remainingServers' = [remainingServers EXCEPT ![self] = remainingServers[self] \ {msg.node}]
                                /\ channels' = [channels EXCEPT ![self] = Tail(channels[self])]
                                /\ pc' = [pc EXCEPT ![self] = "receiveLoop"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "sendDecision"]
                                /\ UNCHANGED << channels, remainingServers >>
                     /\ UNCHANGED << transactionStatus, transactionInfo, 
                                     serverResponses, clientDecisions, 
                                     currentMsg_, currentMsg_c, commitDecision, 
                                     remainingServers_, currentMsg, 
                                     chosenServers >>

sendDecision(self) == /\ pc[self] = "sendDecision"
                      /\ \E decision \in {"Abort", "Commit"}:
                           /\ Len(channels[(currentMsg[self].coord)]) < CASE (currentMsg[self].coord) \in Clients -> ClientQSize
                                                                          [] (currentMsg[self].coord) \in Nodes -> NodeQSize
                                                                          [] (currentMsg[self].coord) \in Coords -> CoordQSize
                           /\ channels' = [channels EXCEPT ![(currentMsg[self].coord)] = Append(channels[(currentMsg[self].coord)], ([id |-> currentMsg[self].id, client |-> self, type |-> "commitReq", decision |-> decision]))]
                      /\ pc' = [pc EXCEPT ![self] = "getFinalDecision"]
                      /\ UNCHANGED << transactionStatus, transactionInfo, 
                                      serverResponses, clientDecisions, 
                                      currentMsg_, currentMsg_c, 
                                      commitDecision, remainingServers_, 
                                      remainingServers, currentMsg, 
                                      chosenServers >>

getFinalDecision(self) == /\ pc[self] = "getFinalDecision"
                          /\ channels[self] /= <<>>
                          /\ LET msg == Head(channels[self]) IN
                               /\ Assert(msg.id = currentMsg[self].id, 
                                         "Failure of assertion at line 226, column 9.")
                               /\ Assert(msg.type = "commitDecision", 
                                         "Failure of assertion at line 227, column 9.")
                               /\ transactionStatus' = [transactionStatus EXCEPT ![self][currentMsg[self].id] = msg.decision]
                          /\ channels' = [channels EXCEPT ![self] = Tail(channels[self])]
                          /\ pc' = [pc EXCEPT ![self] = "clientStart"]
                          /\ UNCHANGED << transactionInfo, serverResponses, 
                                          clientDecisions, currentMsg_, 
                                          currentMsg_c, commitDecision, 
                                          remainingServers_, remainingServers, 
                                          currentMsg, chosenServers >>

clientHandler(self) == clientStart(self) \/ sendLoop(self)
                          \/ sendInfoToCoord(self) \/ receiveLoop(self)
                          \/ sendDecision(self) \/ getFinalDecision(self)

Next == (\E self \in Nodes: nodeHandler(self))
           \/ (\E self \in Coords: coordHandler(self))
           \/ (\E self \in Clients: clientHandler(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(nodeHandler(self))
        /\ \A self \in Coords : WF_vars(coordHandler(self))
        /\ \A self \in Clients : WF_vars(clientHandler(self))

\* END TRANSLATION

\* Invariants
ProcessingInvariant == \A id \in IDSet: \A x, y \in Clients: \/ x = y
                                                             \/ transactionStatus[x][id] /= "Processing"
                                                             \/ transactionStatus[y][id] /= "Processing"

ChannelInvariant == \A p \in ProcSet : Len(channels[p]) <= CASE p \in Clients -> ClientQSize
                                                             [] p \in Nodes -> NodeQSize
                                                             [] p \in Coords -> CoordQSize
                                                             
\*StatusInvariant == \A x \in 1..N:
\*                status[x] = "Committed" \/ status[x] = "Aborted" \/ status[x] = "Prepared" \/ status[x] = "Initiated"
\*                
\*SentReceivedInvariant == \A x \in 1..N:
\*                sent[x] <= NumOfMessages /\ received[x] <= NumOfMessages /\ sent[x] < received[x]
\*                
\*\* Correctness
\*CounterCorrectness == <>(Termination /\ (\A x \in 1..N: sent[x] = NumOfMessages /\ received[x] = NumOfMessages))

=================================
