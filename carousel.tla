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

\* Valid messages
ReadReq == [id: IDSet, client: Clients, type: {"readReq"}, coord: Coords]
ReadRsp == [id: IDSet, type: {"readRsp"}]
TxnInfo == [id: IDSet, client: Clients, type: {"txnInfo"}, servers: SUBSET Nodes \ {{}}]
CommitReq == [id: IDSet, type: {"commitReq"}, decision: {"Commit", "Abort"}]
CommitDecision == [id: IDSet, type: {"commitDecision"}, decision: {"Committed", "Aborted"}]
CommitToNode == [id: IDSet, type: {"commitToNode"}, decision: {"Committed", "Aborted"}]
PrepareRsp == [id: IDSet, type: {"prepareRsp"}, result: {"Prepared", "Aborted"}]
DummyRecord == [type |-> "dummy"]
Message == ReadReq \cup ReadRsp \cup TxnInfo \cup CommitReq \cup CommitDecision \cup CommitToNode \cup PrepareRsp

\* Beginning of PlusCal algorithm
(* --algorithm progress

variables
    \* Each process has its view of the status of a transaction
    transactionStatus = [p \in Clients \cup Nodes \cup Coords |-> [id \in IDSet |-> "Aborted"]],
    \* Information for each transaction, used by coordinators
    \* A coordinator should only read from an entry if it is processing that transaction
    transactionInfo = [id \in IDSet |-> CHOOSE msg \in TxnInfo : msg.id = id],
    serverResponses = [id \in IDSet |-> EmptyBag],
    clientDecisions = [id \in IDSet |-> "Unknown"],
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
    currentNodeMsg = CHOOSE msg \in CommitToNode: msg.decision = "Aborted";
begin
nodeHandlerStart:
while TRUE do
    await channels[self] /= <<>>;
    with msg = Head(channels[self]) do
        currentNodeMsg := msg;
    end with;
    channels[self] := Tail(channels[self]);
     
    nodeProcessMsg:
    if currentNodeMsg.type = "readReq" then
        transactionStatus[self][currentNodeMsg.id] := "Processing";
        send([id |-> currentNodeMsg.id, type |-> "readRsp"], currentNodeMsg.client);
        
        nodeToCoord:
        with prepareResult \in {"Prepared", "Aborted"} do
            send([id |-> currentNodeMsg.id, type |-> "prepareRsp", result |-> prepareResult], currentNodeMsg.coord);
        end with;
     else
        \* assert transactionStatus[self][currentNodeMsg.id] = "Processing";
        transactionStatus[self][currentNodeMsg.id] := currentNodeMsg.decision;
     end if;
end while;
end process;

\* coordinator process
\* Makes final decision about whether a transaction is committed
\* Note that we do not implement the full 2PC algorithm
fair process coordHandler \in Coords
variable
    currentCoordMsg = CHOOSE msg \in CommitReq: msg.decision = "Abort",
    commitDecision = "Aborted",
    remainingServers = {};
begin
coordHandlerStart:
while TRUE do
    await channels[self] /= <<>>;
    with msg = Head(channels[self]) do
        currentCoordMsg := msg;
    end with;
    channels[self] := Tail(channels[self]);
    
    coordProcessMsg:
    if currentCoordMsg.type = "txnInfo" then
        transactionStatus[self][currentCoordMsg.id] := "Processing";
        transactionInfo[currentCoordMsg.id] := currentCoordMsg;    
    elsif currentCoordMsg.type = "prepareRsp" then
        transactionStatus[self][currentCoordMsg.id] := "Processing";
        serverResponses[currentCoordMsg.id] := serverResponses[currentCoordMsg.id] (+) SetToBag({currentCoordMsg.result});
    else
        \* The decision can't be received before the "txnInfo" message
        \* assert transactionStatus[self][currentCoordMsg.id] = "Processing";
        clientDecisions[currentCoordMsg.id] := currentCoordMsg.decision;
    end if;
    
    checkForDecision:
    if /\ transactionInfo[currentCoordMsg.id] /= DummyRecord
       /\ BagCardinality(serverResponses[currentCoordMsg.id]) = Cardinality(transactionInfo[currentCoordMsg.id].servers)
       /\ clientDecisions[currentCoordMsg.id] /= "Unknown" then
        commitDecision := IF /\ BagToSet(serverResponses[currentCoordMsg.id]) = {"Prepared"}
                             /\ clientDecisions[currentCoordMsg.id] = "Commit"
                          THEN "Committed" ELSE "Aborted";
        remainingServers := transactionInfo[currentCoordMsg.id].servers;
        
        sendDecisionToClient:
        with client = transactionInfo[currentCoordMsg.id].client do
            send([id |-> currentCoordMsg.id, type |-> "commitDecision", decision |-> commitDecision], client);
        end with;
        
        sendDecisionToNodes:
        while remainingServers /= {} do
            with server = minProc(remainingServers) do
                send([id |-> currentCoordMsg.id, type |-> "commitToNode", decision |-> commitDecision], server);
                remainingServers := remainingServers \ {server};
            end with;
        end while;
        
        updateCoordStatus:
        transactionStatus[self][currentCoordMsg.id] := commitDecision;
        serverResponses[currentCoordMsg.id] := EmptyBag;
        clientDecisions[currentCoordMsg.id] := "Unknown";
        transactionInfo[currentCoordMsg.id] := DummyRecord;
    end if;
end while;
end process;


\* sender process
\* Processes only one transaction at a time
fair process clientHandler \in Clients
variable
    remainingCount = 0,
    currentClientMsg = CHOOSE msg \in ReadReq: msg.client = self,
    chosenServers = {},
begin
clientStart:
while TRUE do
    await idsInUse /= IDSet;
    with id \in IDSet \ idsInUse, sub \in SUBSET Nodes \ {{}}, coord \in Coords do
        currentClientMsg := [id |-> id, client |-> self, type |-> "readReq", coord |-> coord];
        chosenServers := sub;
        remainingCount := Cardinality(sub);
        transactionStatus[self][id] := "Processing";
    end with;
    
    sendInfoToCoord:
    send([id |-> currentClientMsg.id, client |-> self, type |-> "txnInfo", servers |-> chosenServers], currentClientMsg.coord);

    \* Send message to every server chosen
    sendLoop:
    while chosenServers /= {} do
        with server = minProc(chosenServers) do
            send(currentClientMsg, server);
            chosenServers := chosenServers \ {server};
        end with;
    end while;
    
    receiveLoop:
    while remainingCount /= 0 do
        await channels[self] /= <<>>;
        with msg = Head(channels[self]) do
            \* assert msg.id = currentClientMsg.id;
            \* assert msg \in ReadRsp;
            remainingCount := remainingCount - 1;
        end with;
        channels[self] := Tail(channels[self]);
    end while;
    
    sendDecision:
    with decision \in {"Abort", "Commit"} do
        send([id |-> currentClientMsg.id, type |-> "commitReq", decision |-> decision], currentClientMsg.coord);
    end with;
    
    getFinalDecision:
    await channels[self] /= <<>>;
    with msg = Head(channels[self]) do
        \* assert msg.id = currentClientMsg.id;
        \* assert msg \in CommitDecision;
        transactionStatus[self][currentClientMsg.id] := msg.decision;
    end with;
    channels[self] := Tail(channels[self]);
end while;
end process;

end algorithm *)
\* BEGIN TRANSLATION
VARIABLES transactionStatus, transactionInfo, serverResponses, 
          clientDecisions, channels, pc

(* define statement *)
idsInUse == {id \in IDSet : (\E x \in Clients \cup Nodes \cup Coords :
                             transactionStatus[x][id] = "Processing")}
minProc(procs) == CHOOSE p \in procs : \A q \in procs : p.num <= q.num

VARIABLES currentNodeMsg, currentCoordMsg, commitDecision, remainingServers, 
          remainingCount, currentClientMsg, chosenServers

vars == << transactionStatus, transactionInfo, serverResponses, 
           clientDecisions, channels, pc, currentNodeMsg, currentCoordMsg, 
           commitDecision, remainingServers, remainingCount, currentClientMsg, 
           chosenServers >>

ProcSet == (Nodes) \cup (Coords) \cup (Clients)

Init == (* Global variables *)
        /\ transactionStatus = [p \in Clients \cup Nodes \cup Coords |-> [id \in IDSet |-> "Aborted"]]
        /\ transactionInfo = [id \in IDSet |-> CHOOSE msg \in TxnInfo : msg.id = id]
        /\ serverResponses = [id \in IDSet |-> EmptyBag]
        /\ clientDecisions = [id \in IDSet |-> "Unknown"]
        /\ channels = [x \in Clients \cup Nodes \cup Coords |-> <<>>]
        (* Process nodeHandler *)
        /\ currentNodeMsg = [self \in Nodes |-> CHOOSE msg \in CommitToNode: msg.decision = "Aborted"]
        (* Process coordHandler *)
        /\ currentCoordMsg = [self \in Coords |-> CHOOSE msg \in CommitReq: msg.decision = "Abort"]
        /\ commitDecision = [self \in Coords |-> "Aborted"]
        /\ remainingServers = [self \in Coords |-> {}]
        (* Process clientHandler *)
        /\ remainingCount = [self \in Clients |-> 0]
        /\ currentClientMsg = [self \in Clients |-> CHOOSE msg \in ReadReq: msg.client = self]
        /\ chosenServers = [self \in Clients |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self \in Nodes -> "nodeHandlerStart"
                                        [] self \in Coords -> "coordHandlerStart"
                                        [] self \in Clients -> "clientStart"]

nodeHandlerStart(self) == /\ pc[self] = "nodeHandlerStart"
                          /\ channels[self] /= <<>>
                          /\ LET msg == Head(channels[self]) IN
                               currentNodeMsg' = [currentNodeMsg EXCEPT ![self] = msg]
                          /\ channels' = [channels EXCEPT ![self] = Tail(channels[self])]
                          /\ pc' = [pc EXCEPT ![self] = "nodeProcessMsg"]
                          /\ UNCHANGED << transactionStatus, transactionInfo, 
                                          serverResponses, clientDecisions, 
                                          currentCoordMsg, commitDecision, 
                                          remainingServers, remainingCount, 
                                          currentClientMsg, chosenServers >>

nodeProcessMsg(self) == /\ pc[self] = "nodeProcessMsg"
                        /\ IF currentNodeMsg[self].type = "readReq"
                              THEN /\ transactionStatus' = [transactionStatus EXCEPT ![self][currentNodeMsg[self].id] = "Processing"]
                                   /\ Len(channels[(currentNodeMsg[self].client)]) < CASE (currentNodeMsg[self].client) \in Clients -> ClientQSize
                                                                                       [] (currentNodeMsg[self].client) \in Nodes -> NodeQSize
                                                                                       [] (currentNodeMsg[self].client) \in Coords -> CoordQSize
                                   /\ channels' = [channels EXCEPT ![(currentNodeMsg[self].client)] = Append(channels[(currentNodeMsg[self].client)], ([id |-> currentNodeMsg[self].id, type |-> "readRsp"]))]
                                   /\ pc' = [pc EXCEPT ![self] = "nodeToCoord"]
                              ELSE /\ transactionStatus' = [transactionStatus EXCEPT ![self][currentNodeMsg[self].id] = currentNodeMsg[self].decision]
                                   /\ pc' = [pc EXCEPT ![self] = "nodeHandlerStart"]
                                   /\ UNCHANGED channels
                        /\ UNCHANGED << transactionInfo, serverResponses, 
                                        clientDecisions, currentNodeMsg, 
                                        currentCoordMsg, commitDecision, 
                                        remainingServers, remainingCount, 
                                        currentClientMsg, chosenServers >>

nodeToCoord(self) == /\ pc[self] = "nodeToCoord"
                     /\ \E prepareResult \in {"Prepared", "Aborted"}:
                          /\ Len(channels[(currentNodeMsg[self].coord)]) < CASE (currentNodeMsg[self].coord) \in Clients -> ClientQSize
                                                                             [] (currentNodeMsg[self].coord) \in Nodes -> NodeQSize
                                                                             [] (currentNodeMsg[self].coord) \in Coords -> CoordQSize
                          /\ channels' = [channels EXCEPT ![(currentNodeMsg[self].coord)] = Append(channels[(currentNodeMsg[self].coord)], ([id |-> currentNodeMsg[self].id, type |-> "prepareRsp", result |-> prepareResult]))]
                     /\ pc' = [pc EXCEPT ![self] = "nodeHandlerStart"]
                     /\ UNCHANGED << transactionStatus, transactionInfo, 
                                     serverResponses, clientDecisions, 
                                     currentNodeMsg, currentCoordMsg, 
                                     commitDecision, remainingServers, 
                                     remainingCount, currentClientMsg, 
                                     chosenServers >>

nodeHandler(self) == nodeHandlerStart(self) \/ nodeProcessMsg(self)
                        \/ nodeToCoord(self)

coordHandlerStart(self) == /\ pc[self] = "coordHandlerStart"
                           /\ channels[self] /= <<>>
                           /\ LET msg == Head(channels[self]) IN
                                currentCoordMsg' = [currentCoordMsg EXCEPT ![self] = msg]
                           /\ channels' = [channels EXCEPT ![self] = Tail(channels[self])]
                           /\ pc' = [pc EXCEPT ![self] = "coordProcessMsg"]
                           /\ UNCHANGED << transactionStatus, transactionInfo, 
                                           serverResponses, clientDecisions, 
                                           currentNodeMsg, commitDecision, 
                                           remainingServers, remainingCount, 
                                           currentClientMsg, chosenServers >>

coordProcessMsg(self) == /\ pc[self] = "coordProcessMsg"
                         /\ IF currentCoordMsg[self].type = "txnInfo"
                               THEN /\ transactionStatus' = [transactionStatus EXCEPT ![self][currentCoordMsg[self].id] = "Processing"]
                                    /\ transactionInfo' = [transactionInfo EXCEPT ![currentCoordMsg[self].id] = currentCoordMsg[self]]
                                    /\ UNCHANGED << serverResponses, 
                                                    clientDecisions >>
                               ELSE /\ IF currentCoordMsg[self].type = "prepareRsp"
                                          THEN /\ transactionStatus' = [transactionStatus EXCEPT ![self][currentCoordMsg[self].id] = "Processing"]
                                               /\ serverResponses' = [serverResponses EXCEPT ![currentCoordMsg[self].id] = serverResponses[currentCoordMsg[self].id] (+) SetToBag({currentCoordMsg[self].result})]
                                               /\ UNCHANGED clientDecisions
                                          ELSE /\ clientDecisions' = [clientDecisions EXCEPT ![currentCoordMsg[self].id] = currentCoordMsg[self].decision]
                                               /\ UNCHANGED << transactionStatus, 
                                                               serverResponses >>
                                    /\ UNCHANGED transactionInfo
                         /\ pc' = [pc EXCEPT ![self] = "checkForDecision"]
                         /\ UNCHANGED << channels, currentNodeMsg, 
                                         currentCoordMsg, commitDecision, 
                                         remainingServers, remainingCount, 
                                         currentClientMsg, chosenServers >>

checkForDecision(self) == /\ pc[self] = "checkForDecision"
                          /\ IF /\ transactionInfo[currentCoordMsg[self].id] /= DummyRecord
                                /\ BagCardinality(serverResponses[currentCoordMsg[self].id]) = Cardinality(transactionInfo[currentCoordMsg[self].id].servers)
                                /\ clientDecisions[currentCoordMsg[self].id] /= "Unknown"
                                THEN /\ commitDecision' = [commitDecision EXCEPT ![self] = IF /\ BagToSet(serverResponses[currentCoordMsg[self].id]) = {"Prepared"}
                                                                                              /\ clientDecisions[currentCoordMsg[self].id] = "Commit"
                                                                                           THEN "Committed" ELSE "Aborted"]
                                     /\ remainingServers' = [remainingServers EXCEPT ![self] = transactionInfo[currentCoordMsg[self].id].servers]
                                     /\ pc' = [pc EXCEPT ![self] = "sendDecisionToClient"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "coordHandlerStart"]
                                     /\ UNCHANGED << commitDecision, 
                                                     remainingServers >>
                          /\ UNCHANGED << transactionStatus, transactionInfo, 
                                          serverResponses, clientDecisions, 
                                          channels, currentNodeMsg, 
                                          currentCoordMsg, remainingCount, 
                                          currentClientMsg, chosenServers >>

sendDecisionToClient(self) == /\ pc[self] = "sendDecisionToClient"
                              /\ LET client == transactionInfo[currentCoordMsg[self].id].client IN
                                   /\ Len(channels[client]) < CASE client \in Clients -> ClientQSize
                                                                [] client \in Nodes -> NodeQSize
                                                                [] client \in Coords -> CoordQSize
                                   /\ channels' = [channels EXCEPT ![client] = Append(channels[client], ([id |-> currentCoordMsg[self].id, type |-> "commitDecision", decision |-> commitDecision[self]]))]
                              /\ pc' = [pc EXCEPT ![self] = "sendDecisionToNodes"]
                              /\ UNCHANGED << transactionStatus, 
                                              transactionInfo, serverResponses, 
                                              clientDecisions, currentNodeMsg, 
                                              currentCoordMsg, commitDecision, 
                                              remainingServers, remainingCount, 
                                              currentClientMsg, chosenServers >>

sendDecisionToNodes(self) == /\ pc[self] = "sendDecisionToNodes"
                             /\ IF remainingServers[self] /= {}
                                   THEN /\ LET server == minProc(remainingServers[self]) IN
                                             /\ Len(channels[server]) < CASE server \in Clients -> ClientQSize
                                                                          [] server \in Nodes -> NodeQSize
                                                                          [] server \in Coords -> CoordQSize
                                             /\ channels' = [channels EXCEPT ![server] = Append(channels[server], ([id |-> currentCoordMsg[self].id, type |-> "commitToNode", decision |-> commitDecision[self]]))]
                                             /\ remainingServers' = [remainingServers EXCEPT ![self] = remainingServers[self] \ {server}]
                                        /\ pc' = [pc EXCEPT ![self] = "sendDecisionToNodes"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "updateCoordStatus"]
                                        /\ UNCHANGED << channels, 
                                                        remainingServers >>
                             /\ UNCHANGED << transactionStatus, 
                                             transactionInfo, serverResponses, 
                                             clientDecisions, currentNodeMsg, 
                                             currentCoordMsg, commitDecision, 
                                             remainingCount, currentClientMsg, 
                                             chosenServers >>

updateCoordStatus(self) == /\ pc[self] = "updateCoordStatus"
                           /\ transactionStatus' = [transactionStatus EXCEPT ![self][currentCoordMsg[self].id] = commitDecision[self]]
                           /\ serverResponses' = [serverResponses EXCEPT ![currentCoordMsg[self].id] = EmptyBag]
                           /\ clientDecisions' = [clientDecisions EXCEPT ![currentCoordMsg[self].id] = "Unknown"]
                           /\ transactionInfo' = [transactionInfo EXCEPT ![currentCoordMsg[self].id] = DummyRecord]
                           /\ pc' = [pc EXCEPT ![self] = "coordHandlerStart"]
                           /\ UNCHANGED << channels, currentNodeMsg, 
                                           currentCoordMsg, commitDecision, 
                                           remainingServers, remainingCount, 
                                           currentClientMsg, chosenServers >>

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
                              /\ currentClientMsg' = [currentClientMsg EXCEPT ![self] = [id |-> id, client |-> self, type |-> "readReq", coord |-> coord]]
                              /\ chosenServers' = [chosenServers EXCEPT ![self] = sub]
                              /\ remainingCount' = [remainingCount EXCEPT ![self] = Cardinality(sub)]
                              /\ transactionStatus' = [transactionStatus EXCEPT ![self][id] = "Processing"]
                     /\ pc' = [pc EXCEPT ![self] = "sendInfoToCoord"]
                     /\ UNCHANGED << transactionInfo, serverResponses, 
                                     clientDecisions, channels, currentNodeMsg, 
                                     currentCoordMsg, commitDecision, 
                                     remainingServers >>

sendInfoToCoord(self) == /\ pc[self] = "sendInfoToCoord"
                         /\ Len(channels[(currentClientMsg[self].coord)]) < CASE (currentClientMsg[self].coord) \in Clients -> ClientQSize
                                                                              [] (currentClientMsg[self].coord) \in Nodes -> NodeQSize
                                                                              [] (currentClientMsg[self].coord) \in Coords -> CoordQSize
                         /\ channels' = [channels EXCEPT ![(currentClientMsg[self].coord)] = Append(channels[(currentClientMsg[self].coord)], ([id |-> currentClientMsg[self].id, client |-> self, type |-> "txnInfo", servers |-> chosenServers[self]]))]
                         /\ pc' = [pc EXCEPT ![self] = "sendLoop"]
                         /\ UNCHANGED << transactionStatus, transactionInfo, 
                                         serverResponses, clientDecisions, 
                                         currentNodeMsg, currentCoordMsg, 
                                         commitDecision, remainingServers, 
                                         remainingCount, currentClientMsg, 
                                         chosenServers >>

sendLoop(self) == /\ pc[self] = "sendLoop"
                  /\ IF chosenServers[self] /= {}
                        THEN /\ LET server == minProc(chosenServers[self]) IN
                                  /\ Len(channels[server]) < CASE server \in Clients -> ClientQSize
                                                               [] server \in Nodes -> NodeQSize
                                                               [] server \in Coords -> CoordQSize
                                  /\ channels' = [channels EXCEPT ![server] = Append(channels[server], currentClientMsg[self])]
                                  /\ chosenServers' = [chosenServers EXCEPT ![self] = chosenServers[self] \ {server}]
                             /\ pc' = [pc EXCEPT ![self] = "sendLoop"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "receiveLoop"]
                             /\ UNCHANGED << channels, chosenServers >>
                  /\ UNCHANGED << transactionStatus, transactionInfo, 
                                  serverResponses, clientDecisions, 
                                  currentNodeMsg, currentCoordMsg, 
                                  commitDecision, remainingServers, 
                                  remainingCount, currentClientMsg >>

receiveLoop(self) == /\ pc[self] = "receiveLoop"
                     /\ IF remainingCount[self] /= 0
                           THEN /\ channels[self] /= <<>>
                                /\ LET msg == Head(channels[self]) IN
                                     remainingCount' = [remainingCount EXCEPT ![self] = remainingCount[self] - 1]
                                /\ channels' = [channels EXCEPT ![self] = Tail(channels[self])]
                                /\ pc' = [pc EXCEPT ![self] = "receiveLoop"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "sendDecision"]
                                /\ UNCHANGED << channels, remainingCount >>
                     /\ UNCHANGED << transactionStatus, transactionInfo, 
                                     serverResponses, clientDecisions, 
                                     currentNodeMsg, currentCoordMsg, 
                                     commitDecision, remainingServers, 
                                     currentClientMsg, chosenServers >>

sendDecision(self) == /\ pc[self] = "sendDecision"
                      /\ \E decision \in {"Abort", "Commit"}:
                           /\ Len(channels[(currentClientMsg[self].coord)]) < CASE (currentClientMsg[self].coord) \in Clients -> ClientQSize
                                                                                [] (currentClientMsg[self].coord) \in Nodes -> NodeQSize
                                                                                [] (currentClientMsg[self].coord) \in Coords -> CoordQSize
                           /\ channels' = [channels EXCEPT ![(currentClientMsg[self].coord)] = Append(channels[(currentClientMsg[self].coord)], ([id |-> currentClientMsg[self].id, type |-> "commitReq", decision |-> decision]))]
                      /\ pc' = [pc EXCEPT ![self] = "getFinalDecision"]
                      /\ UNCHANGED << transactionStatus, transactionInfo, 
                                      serverResponses, clientDecisions, 
                                      currentNodeMsg, currentCoordMsg, 
                                      commitDecision, remainingServers, 
                                      remainingCount, currentClientMsg, 
                                      chosenServers >>

getFinalDecision(self) == /\ pc[self] = "getFinalDecision"
                          /\ channels[self] /= <<>>
                          /\ LET msg == Head(channels[self]) IN
                               transactionStatus' = [transactionStatus EXCEPT ![self][currentClientMsg[self].id] = msg.decision]
                          /\ channels' = [channels EXCEPT ![self] = Tail(channels[self])]
                          /\ pc' = [pc EXCEPT ![self] = "clientStart"]
                          /\ UNCHANGED << transactionInfo, serverResponses, 
                                          clientDecisions, currentNodeMsg, 
                                          currentCoordMsg, commitDecision, 
                                          remainingServers, remainingCount, 
                                          currentClientMsg, chosenServers >>

clientHandler(self) == clientStart(self) \/ sendInfoToCoord(self)
                          \/ sendLoop(self) \/ receiveLoop(self)
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
ProcessingInvariant == \A id \in IDSet: /\ \A x, y \in Clients: \/ x = y
                                                                \/ transactionStatus[x][id] /= "Processing"
                                                                \/ transactionStatus[y][id] /= "Processing"
                                        /\ \A x, y \in Coords:  \/ x = y
                                                                \/ transactionStatus[x][id] /= "Processing"
                                                                \/ transactionStatus[y][id] /= "Processing"
                                                  

ChannelInvariant == \A p \in ProcSet : Len(channels[p]) <= CASE p \in Clients -> ClientQSize
                                                             [] p \in Nodes -> NodeQSize
                                                             [] p \in Coords -> CoordQSize

TypeInvariant == /\ transactionStatus \in [ProcSet -> [IDSet -> {"Committed", "Aborted", "Processing"}]]
                 /\ transactionInfo \in [IDSet -> TxnInfo \cup {DummyRecord}]
                 /\ serverResponses \in [IDSet -> SubBag([x \in {"Prepared", "Aborted"} |-> N])]
                 /\ clientDecisions \in [IDSet -> {"Unknown", "Commit", "Abort"}]
                 /\ channels \in [ProcSet -> Seq(Message)]
                 /\ \A self \in Clients: /\ remainingCount[self] \in 0..N
                                         /\ currentClientMsg[self] \in ReadReq
                                         /\ chosenServers[self] \in SUBSET Nodes
                 /\ \A self \in Nodes: /\ currentNodeMsg[self] \in ReadReq \cup CommitToNode
                 /\ \A self \in Coords: /\ currentCoordMsg[self] \in TxnInfo \cup CommitReq \cup PrepareRsp
                                        /\ commitDecision[self] \in {"Committed", "Aborted"}
                                        /\ remainingServers[self] \in SUBSET Nodes
                                                             
\*StatusInvariant == \A x \in 1..N:
\*                status[x] = "Committed" \/ status[x] = "Aborted" \/ status[x] = "Prepared" \/ status[x] = "Initiated"
\*                
\*SentReceivedInvariant == \A x \in 1..N:
\*                sent[x] <= NumOfMessages /\ received[x] <= NumOfMessages /\ sent[x] < received[x]
\*                
\*\* Correctness
\*CounterCorrectness == <>(Termination /\ (\A x \in 1..N: sent[x] = NumOfMessages /\ received[x] = NumOfMessages))

=================================
