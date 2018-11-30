------------------------------- MODULE carousel -------------------------------

(***************************************************************************)
(* This is a TLA+ specification of the Carousel protocol.                  *)
(***************************************************************************)

\* Overview
\* There are 3 concurrent processes in this spec.

EXTENDS Naturals, FiniteSets, Sequences, TLC
CONSTANT C, N

ASSUME C \in Nat /\ C > 0
ASSUME N \in Nat /\ N > 0
Clients == 1..C
Nodes == 1..N

(* --algorithm progress
variable
  IDSet = <<1,2,3,4,5,6,7,8>>,
  \* Status of each node
  status = [n \in Nodes |-> "Init"],
  
  sent = [n \in Nodes |-> 0],
  received = [n \in Nodes |-> 0],
  channels = [n \in Nodes |-> <<>>],
  inChannels = [c \in Clients |-> <<>>],
  expectedResponses = [c \in Clients |-> 0],

\* Queue macros
macro recv(queue, receiver)
begin
  receiver := Head(queue);
  queue := Tail(queue);
end macro

macro send(queue, message)
begin
  queue := Append(queue, message);
end macro


\* Client
procedure sendClientMessage(id, client, server)
variable
    msg;
begin
  P1:
    msg := [id |-> id, client |-> client];
    send(channels[server], msg);
    sent[server] := sent[server] + 1;
end procedure


procedure updateStatus(node)
variable
    serverMsg,
    incomingMsg,
    msgId,
    clientId,
    serverStatus;
begin
  P1:
    recv(channels[node], incomingMsg);
    msgId := incomingMsg.id;
    clientId := incomingMsg.client;
    
    either
    \*    Commit
      serverStatus := "Committed";
      received[node] := received[node] + 1;
      status[node] := serverStatus;
    or
    \*    Abort
      serverStatus := "Aborted";
    end either;
    
    \*    Send message back
    serverMsg := [id |-> msgId, serverStatus |-> serverStatus];
    send(inChannels[clientId], serverMsg);
end procedure


procedure sendClientMessagesToServers(client, serverSet)
variable 
    id;
begin
  GetID:
    \* Get ID from IDSet and remove it from IDSet
    await IDSet /= <<>>;  \* First check if IDSet is empty, if not, wait
    id := Head(IDSet);
    IDSet := Tail(IDSet);
    
    \* Set the number of client's expected responses
    expectedResponses[client] := Cardinality(serverSet);
  SendMessages:
\*    while serverSet /= {} do
        with selectedServer \in serverSet do
            \*  Remove selected from serverSet
            serverSet := serverSet \ {selectedServer};
            call sendClientMessage(id, client, selectedServer);
        end with;
\*    end while;
end procedure


fair process sendClientMessages \in Clients
variables
    msg,
    head,
    subsets = SUBSET Nodes \ {{}};
begin
    sendClientMessages:
      while TRUE do
        with chosenSet \in subsets do
            call sendClientMessagesToServers(self, chosenSet);
        end with;
      end while;
end process;


fair process nodeHandler \in Nodes
variable
  message = "";
begin
  nodeHandler:
    while TRUE do
      await channels[self] /= <<>>;
      call updateStatus(self);
    end while;
end process;


fair process clientHandler \in Clients
variable
  inMsg,
  serverStatus;
begin
  clientHandler:
    while TRUE do
      await inChannels[self] /= <<>>;
      recv(inChannels[self], inMsg);
      
      \* Recycle ID if all expected responses received
      expectedResponses[client] := expectedResponses[client] - 1;
      if expectedResponses[client] = 0 then
        IDSet := Append(IDSet, inMsg.id);
      end if;
      
      serverStatus := inMsg.serverStatus;
\*      Assert serverStatus = status[server];
    end while;
end process;

end algorithm *)
\* BEGIN TRANSLATION
\* Label P1 of procedure sendClientMessage at line 49 col 5 changed to P1_
\* Label sendClientMessages of process sendClientMessages at line 114 col 7 changed to sendClientMessages_
\* Label nodeHandler of process nodeHandler at line 127 col 5 changed to nodeHandler_
\* Label clientHandler of process clientHandler at line 140 col 5 changed to clientHandler_
\* Process variable msg of process sendClientMessages at line 109 col 5 changed to msg_
\* Process variable serverStatus of process clientHandler at line 137 col 3 changed to serverStatus_
\* Procedure variable id of procedure sendClientMessagesToServers at line 86 col 5 changed to id_
\* Parameter client of procedure sendClientMessage at line 44 col 33 changed to client_
CONSTANT defaultInitValue
VARIABLES IDSet, status, sent, received, channels, inChannels, 
          expectedResponses, pc, stack, id, client_, server, msg, node, 
          serverMsg, incomingMsg, msgId, clientId, serverStatus, client, 
          serverSet, id_, msg_, head, subsets, message, inMsg, serverStatus_

vars == << IDSet, status, sent, received, channels, inChannels, 
           expectedResponses, pc, stack, id, client_, server, msg, node, 
           serverMsg, incomingMsg, msgId, clientId, serverStatus, client, 
           serverSet, id_, msg_, head, subsets, message, inMsg, serverStatus_
        >>

ProcSet == (Clients) \cup (Nodes) \cup (Clients)

Init == (* Global variables *)
        /\ IDSet = <<1,2,3,4,5,6,7,8>>
        /\ status = [n \in Nodes |-> "Init"]
        /\ sent = [n \in Nodes |-> 0]
        /\ received = [n \in Nodes |-> 0]
        /\ channels = [n \in Nodes |-> <<>>]
        /\ inChannels = [c \in Clients |-> <<>>]
        /\ expectedResponses = [c \in Clients |-> 0]
        (* Procedure sendClientMessage *)
        /\ id = [ self \in ProcSet |-> defaultInitValue]
        /\ client_ = [ self \in ProcSet |-> defaultInitValue]
        /\ server = [ self \in ProcSet |-> defaultInitValue]
        /\ msg = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure updateStatus *)
        /\ node = [ self \in ProcSet |-> defaultInitValue]
        /\ serverMsg = [ self \in ProcSet |-> defaultInitValue]
        /\ incomingMsg = [ self \in ProcSet |-> defaultInitValue]
        /\ msgId = [ self \in ProcSet |-> defaultInitValue]
        /\ clientId = [ self \in ProcSet |-> defaultInitValue]
        /\ serverStatus = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure sendClientMessagesToServers *)
        /\ client = [ self \in ProcSet |-> defaultInitValue]
        /\ serverSet = [ self \in ProcSet |-> defaultInitValue]
        /\ id_ = [ self \in ProcSet |-> defaultInitValue]
        (* Process sendClientMessages *)
        /\ msg_ = [self \in Clients |-> defaultInitValue]
        /\ head = [self \in Clients |-> defaultInitValue]
        /\ subsets = [self \in Clients |-> SUBSET Nodes \ {{}}]
        (* Process nodeHandler *)
        /\ message = [self \in Nodes |-> ""]
        (* Process clientHandler *)
        /\ inMsg = [self \in Clients |-> defaultInitValue]
        /\ serverStatus_ = [self \in Clients |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "sendClientMessages_"
                                        [] self \in Nodes -> "nodeHandler_"
                                        [] self \in Clients -> "clientHandler_"]

P1_(self) == /\ pc[self] = "P1_"
             /\ msg' = [msg EXCEPT ![self] = [id |-> id[self], client |-> client_[self]]]
             /\ channels' = [channels EXCEPT ![server[self]] = Append((channels[server[self]]), msg'[self])]
             /\ sent' = [sent EXCEPT ![server[self]] = sent[server[self]] + 1]
             /\ pc' = [pc EXCEPT ![self] = "Error"]
             /\ UNCHANGED << IDSet, status, received, inChannels, 
                             expectedResponses, stack, id, client_, server, 
                             node, serverMsg, incomingMsg, msgId, clientId, 
                             serverStatus, client, serverSet, id_, msg_, head, 
                             subsets, message, inMsg, serverStatus_ >>

sendClientMessage(self) == P1_(self)

P1(self) == /\ pc[self] = "P1"
            /\ incomingMsg' = [incomingMsg EXCEPT ![self] = Head((channels[node[self]]))]
            /\ channels' = [channels EXCEPT ![node[self]] = Tail((channels[node[self]]))]
            /\ msgId' = [msgId EXCEPT ![self] = incomingMsg'[self].id]
            /\ clientId' = [clientId EXCEPT ![self] = incomingMsg'[self].client]
            /\ \/ /\ serverStatus' = [serverStatus EXCEPT ![self] = "Committed"]
                  /\ received' = [received EXCEPT ![node[self]] = received[node[self]] + 1]
                  /\ status' = [status EXCEPT ![node[self]] = serverStatus'[self]]
               \/ /\ serverStatus' = [serverStatus EXCEPT ![self] = "Aborted"]
                  /\ UNCHANGED <<status, received>>
            /\ serverMsg' = [serverMsg EXCEPT ![self] = [id |-> msgId'[self], serverStatus |-> serverStatus'[self]]]
            /\ inChannels' = [inChannels EXCEPT ![clientId'[self]] = Append((inChannels[clientId'[self]]), serverMsg'[self])]
            /\ pc' = [pc EXCEPT ![self] = "Error"]
            /\ UNCHANGED << IDSet, sent, expectedResponses, stack, id, client_, 
                            server, msg, node, client, serverSet, id_, msg_, 
                            head, subsets, message, inMsg, serverStatus_ >>

updateStatus(self) == P1(self)

GetID(self) == /\ pc[self] = "GetID"
               /\ IDSet /= <<>>
               /\ id_' = [id_ EXCEPT ![self] = Head(IDSet)]
               /\ IDSet' = Tail(IDSet)
               /\ expectedResponses' = [expectedResponses EXCEPT ![client[self]] = Cardinality(serverSet[self])]
               /\ pc' = [pc EXCEPT ![self] = "SendMessages"]
               /\ UNCHANGED << status, sent, received, channels, inChannels, 
                               stack, id, client_, server, msg, node, 
                               serverMsg, incomingMsg, msgId, clientId, 
                               serverStatus, client, serverSet, msg_, head, 
                               subsets, message, inMsg, serverStatus_ >>

SendMessages(self) == /\ pc[self] = "SendMessages"
                      /\ \E selectedServer \in serverSet[self]:
                           /\ serverSet' = [serverSet EXCEPT ![self] = serverSet[self] \ {selectedServer}]
                           /\ /\ client_' = [client_ EXCEPT ![self] = client[self]]
                              /\ id' = [id EXCEPT ![self] = id_[self]]
                              /\ server' = [server EXCEPT ![self] = selectedServer]
                              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "sendClientMessage",
                                                                       pc        |->  "Error",
                                                                       msg       |->  msg[self],
                                                                       id        |->  id[self],
                                                                       client_   |->  client_[self],
                                                                       server    |->  server[self] ] >>
                                                                   \o stack[self]]
                           /\ msg' = [msg EXCEPT ![self] = defaultInitValue]
                           /\ pc' = [pc EXCEPT ![self] = "P1_"]
                      /\ UNCHANGED << IDSet, status, sent, received, channels, 
                                      inChannels, expectedResponses, node, 
                                      serverMsg, incomingMsg, msgId, clientId, 
                                      serverStatus, client, id_, msg_, head, 
                                      subsets, message, inMsg, serverStatus_ >>

sendClientMessagesToServers(self) == GetID(self) \/ SendMessages(self)

sendClientMessages_(self) == /\ pc[self] = "sendClientMessages_"
                             /\ \E chosenSet \in subsets[self]:
                                  /\ /\ client' = [client EXCEPT ![self] = self]
                                     /\ serverSet' = [serverSet EXCEPT ![self] = chosenSet]
                                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "sendClientMessagesToServers",
                                                                              pc        |->  "sendClientMessages_",
                                                                              id_       |->  id_[self],
                                                                              client    |->  client[self],
                                                                              serverSet |->  serverSet[self] ] >>
                                                                          \o stack[self]]
                                  /\ id_' = [id_ EXCEPT ![self] = defaultInitValue]
                                  /\ pc' = [pc EXCEPT ![self] = "GetID"]
                             /\ UNCHANGED << IDSet, status, sent, received, 
                                             channels, inChannels, 
                                             expectedResponses, id, client_, 
                                             server, msg, node, serverMsg, 
                                             incomingMsg, msgId, clientId, 
                                             serverStatus, msg_, head, subsets, 
                                             message, inMsg, serverStatus_ >>

sendClientMessages(self) == sendClientMessages_(self)

nodeHandler_(self) == /\ pc[self] = "nodeHandler_"
                      /\ channels[self] /= <<>>
                      /\ /\ node' = [node EXCEPT ![self] = self]
                         /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "updateStatus",
                                                                  pc        |->  "nodeHandler_",
                                                                  serverMsg |->  serverMsg[self],
                                                                  incomingMsg |->  incomingMsg[self],
                                                                  msgId     |->  msgId[self],
                                                                  clientId  |->  clientId[self],
                                                                  serverStatus |->  serverStatus[self],
                                                                  node      |->  node[self] ] >>
                                                              \o stack[self]]
                      /\ serverMsg' = [serverMsg EXCEPT ![self] = defaultInitValue]
                      /\ incomingMsg' = [incomingMsg EXCEPT ![self] = defaultInitValue]
                      /\ msgId' = [msgId EXCEPT ![self] = defaultInitValue]
                      /\ clientId' = [clientId EXCEPT ![self] = defaultInitValue]
                      /\ serverStatus' = [serverStatus EXCEPT ![self] = defaultInitValue]
                      /\ pc' = [pc EXCEPT ![self] = "P1"]
                      /\ UNCHANGED << IDSet, status, sent, received, channels, 
                                      inChannels, expectedResponses, id, 
                                      client_, server, msg, client, serverSet, 
                                      id_, msg_, head, subsets, message, inMsg, 
                                      serverStatus_ >>

nodeHandler(self) == nodeHandler_(self)

clientHandler_(self) == /\ pc[self] = "clientHandler_"
                        /\ inChannels[self] /= <<>>
                        /\ inMsg' = [inMsg EXCEPT ![self] = Head((inChannels[self]))]
                        /\ inChannels' = [inChannels EXCEPT ![self] = Tail((inChannels[self]))]
                        /\ expectedResponses' = [expectedResponses EXCEPT ![client[self]] = expectedResponses[client[self]] - 1]
                        /\ IF expectedResponses'[client[self]] = 0
                              THEN /\ IDSet' = Append(IDSet, inMsg'[self].id)
                              ELSE /\ TRUE
                                   /\ IDSet' = IDSet
                        /\ serverStatus_' = [serverStatus_ EXCEPT ![self] = inMsg'[self].serverStatus]
                        /\ pc' = [pc EXCEPT ![self] = "clientHandler_"]
                        /\ UNCHANGED << status, sent, received, channels, 
                                        stack, id, client_, server, msg, node, 
                                        serverMsg, incomingMsg, msgId, 
                                        clientId, serverStatus, client, 
                                        serverSet, id_, msg_, head, subsets, 
                                        message >>

clientHandler(self) == clientHandler_(self)

Next == (\E self \in ProcSet:  \/ sendClientMessage(self)
                               \/ updateStatus(self)
                               \/ sendClientMessagesToServers(self))
           \/ (\E self \in Clients: sendClientMessages(self))
           \/ (\E self \in Nodes: nodeHandler(self))
           \/ (\E self \in Clients: clientHandler(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Clients : /\ WF_vars(sendClientMessages(self))
                                 /\ WF_vars(sendClientMessagesToServers(self))
                                 /\ WF_vars(sendClientMessage(self))
        /\ \A self \in Nodes : WF_vars(nodeHandler(self)) /\ WF_vars(updateStatus(self))
        /\ \A self \in Clients : WF_vars(clientHandler(self))

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
