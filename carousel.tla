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
CONSTANT C, N
ASSUME C \in Nat /\ C > 0
ASSUME N \in Nat /\ N > 0

\* Clients and Nodes as sets
Clients == {<<i, "C">> : i \in 1..C}
Nodes == {<<i, "N">> : i \in 1..N}

InitIdSet == <<1,2,3,4,5,6,7,8>>

\* Beginning of PlusCal algorithm
(* --algorithm progress

variable
  \* IDSet contains all the IDs this model should have
  \* Transaction IDs will be taken out of this set, and put back after they are processed
  \* Should be implemented as a queue so that the queue macros can be used
  \* TODO: Find a way to construct a mapping between IDs and expectedResponses
  IDSet = <<1,2,3,4,5,6,7,8>>,
  
  \* Status of each Node, Init is the default status
  status = [n \in Nodes |-> "Init"],
  
  \* Arrays to keep track of the number of sent and received messages; For invariants/correctness
  sent = [n \in Nodes |-> 0],
  received = [n \in Nodes |-> 0],
  
  \* in and out channels implemented as mappings between Nodes/Clients to their respective queues
  channels = [n \in Nodes |-> <<>>],
  inChannels = [c \in Clients |-> <<>>],
  
  \* expectedResponse is a mapping between each ID in the IDSet and the number of responses
  \* the transaction corresponding to that ID is expecting from its Nodes
  \* See TODO above
  expectedResponses = [i \in DOMAIN IDSet |-> 0],


\* Queue macros
\* recv dequeues queue and populates receiver with the head of queue
macro recv(queue, receiver)
begin
  receiver := Head(queue);
  queue := Tail(queue);
end macro

\* send enqueues queue (appends queue with message)
macro send(queue, message)
begin
  queue := Append(queue, message);
end macro


\* Procedures are analogical to functions
\* sendClientMessage sends a message with fields id and client to specified server
procedure sendClientMessage(id, client, server)
variable
    msg;
begin
  SendClientMessage:
    msg := [id |-> id, client |-> client];
    send(channels[server], msg);
    sent[server] := sent[server] + 1;
end procedure


\* updateStatus receives a message from node's in channel, retrieves id and clientId,
\* and makes a decision whether to commit or abort and makes that its serverStatus.
\* It them sends a server message back to the originating client to tell it its serverStatus,
\* via its out channel.
procedure updateStatus(node)
variable
    serverMsg,
    incomingMsg,
    msgId,
    clientId,
    serverStatus;
begin
  UpdateStatus:
    recv(channels[node], incomingMsg);
    msgId := incomingMsg.id;
    clientId := incomingMsg.client;
    
   u1:
    either
    \*    Commit
      serverStatus := "Committed";
      received[node] := received[node] + 1;
      status[node] := serverStatus;
    or
    \*    Abort
      serverStatus := "Aborted";
    end either;
    
    u2:
    \*    Send message back
    serverMsg := [id |-> msgId, serverStatus |-> serverStatus];
    u3:
    send(inChannels[clientId], serverMsg);
end procedure


\* Send a message to every server in serverSet from the specified client
procedure sendClientMessagesToServers(client, serverSet)
variable 
    id;
begin
  GetID:
    \* Get ID from IDSet and remove it from IDSet
    await IDSet /= <<>>;  \* First check if IDSet is empty, if not, wait
    id := Head(IDSet) || IDSet := Tail(IDSet);
    
    \* Set the number of client's expected responses
    scm1:
    expectedResponses[id] := Cardinality(serverSet);
  SendMessages:
    while serverSet /= {} do
        scm2:
        with selectedServer \in serverSet do
            \*  Remove selected from serverSet
            serverSet := serverSet \ {selectedServer};
            call sendClientMessage(id, client, selectedServer);
        end with;
        CallLabel: print client;
    end while;
end procedure


\* receiver process 
fair process nodeHandler \in Nodes
variable
  message = "";
begin
  NodeStart:
    while TRUE do
      await channels[self] /= <<>>;
      n1: call updateStatus(self);
    end while;
end process;


\* sender process
fair process clientHandler \in Clients
variable
  msg,
  head,
  subsets = SUBSET Nodes \ {{}},
  inMsg,
  serverStatus;
begin
  ClientStart:
  while TRUE do
    c1:
    either
       SendToServer: with chosenSet \in subsets do
            call sendClientMessagesToServers(self, chosenSet);
       end with;
    or 
        await inChannels[self] /= <<>>;
        ReceiveResponse: recv(inChannels[self], inMsg);
      
        \* Recycle ID if all expected responses received
        c4: expectedResponses[inMsg.id] := expectedResponses[inMsg.id] - 1;
        c5: if expectedResponses[inMsg.id] = 0 then
            IDSet := Append(IDSet, inMsg.id);
        end if;
      
        c6: serverStatus := inMsg.serverStatus;
        \* Assert serverStatus = status[server];
    end either;
  end while;
end process;

end algorithm *)
\* BEGIN TRANSLATION
\* Process variable msg of process clientHandler at line 181 col 3 changed to msg_
\* Process variable serverStatus of process clientHandler at line 185 col 3 changed to serverStatus_
\* Procedure variable id of procedure sendClientMessagesToServers at line 142 col 5 changed to id_
\* Parameter client of procedure sendClientMessage at line 92 col 33 changed to client_
CONSTANT defaultInitValue
VARIABLES IDSet, status, sent, received, channels, inChannels, 
          expectedResponses, pc, stack, id, client_, server, msg, node, 
          serverMsg, incomingMsg, msgId, clientId, serverStatus, client, 
          serverSet, id_, message, msg_, head, subsets, inMsg, serverStatus_

vars == << IDSet, status, sent, received, channels, inChannels, 
           expectedResponses, pc, stack, id, client_, server, msg, node, 
           serverMsg, incomingMsg, msgId, clientId, serverStatus, client, 
           serverSet, id_, message, msg_, head, subsets, inMsg, serverStatus_
        >>

ProcSet == (Nodes) \cup (Clients)

Init == (* Global variables *)
        /\ IDSet = <<1,2,3,4,5,6,7,8>>
        /\ status = [n \in Nodes |-> "Init"]
        /\ sent = [n \in Nodes |-> 0]
        /\ received = [n \in Nodes |-> 0]
        /\ channels = [n \in Nodes |-> <<>>]
        /\ inChannels = [c \in Clients |-> <<>>]
        /\ expectedResponses = [i \in DOMAIN IDSet |-> 0]
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
        (* Process nodeHandler *)
        /\ message = [self \in Nodes |-> ""]
        (* Process clientHandler *)
        /\ msg_ = [self \in Clients |-> defaultInitValue]
        /\ head = [self \in Clients |-> defaultInitValue]
        /\ subsets = [self \in Clients |-> SUBSET Nodes \ {{}}]
        /\ inMsg = [self \in Clients |-> defaultInitValue]
        /\ serverStatus_ = [self \in Clients |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Nodes -> "NodeStart"
                                        [] self \in Clients -> "ClientStart"]

SendClientMessage(self) == /\ pc[self] = "SendClientMessage"
                           /\ msg' = [msg EXCEPT ![self] = [id |-> id[self], client |-> client_[self]]]
                           /\ channels' = [channels EXCEPT ![server[self]] = Append((channels[server[self]]), msg'[self])]
                           /\ sent' = [sent EXCEPT ![server[self]] = sent[server[self]] + 1]
                           /\ pc' = [pc EXCEPT ![self] = "Error"]
                           /\ UNCHANGED << IDSet, status, received, inChannels, 
                                           expectedResponses, stack, id, 
                                           client_, server, node, serverMsg, 
                                           incomingMsg, msgId, clientId, 
                                           serverStatus, client, serverSet, 
                                           id_, message, msg_, head, subsets, 
                                           inMsg, serverStatus_ >>

sendClientMessage(self) == SendClientMessage(self)

UpdateStatus(self) == /\ pc[self] = "UpdateStatus"
                      /\ incomingMsg' = [incomingMsg EXCEPT ![self] = Head((channels[node[self]]))]
                      /\ channels' = [channels EXCEPT ![node[self]] = Tail((channels[node[self]]))]
                      /\ msgId' = [msgId EXCEPT ![self] = incomingMsg'[self].id]
                      /\ clientId' = [clientId EXCEPT ![self] = incomingMsg'[self].client]
                      /\ pc' = [pc EXCEPT ![self] = "u1"]
                      /\ UNCHANGED << IDSet, status, sent, received, 
                                      inChannels, expectedResponses, stack, id, 
                                      client_, server, msg, node, serverMsg, 
                                      serverStatus, client, serverSet, id_, 
                                      message, msg_, head, subsets, inMsg, 
                                      serverStatus_ >>

u1(self) == /\ pc[self] = "u1"
            /\ \/ /\ serverStatus' = [serverStatus EXCEPT ![self] = "Committed"]
                  /\ received' = [received EXCEPT ![node[self]] = received[node[self]] + 1]
                  /\ status' = [status EXCEPT ![node[self]] = serverStatus'[self]]
               \/ /\ serverStatus' = [serverStatus EXCEPT ![self] = "Aborted"]
                  /\ UNCHANGED <<status, received>>
            /\ pc' = [pc EXCEPT ![self] = "u2"]
            /\ UNCHANGED << IDSet, sent, channels, inChannels, 
                            expectedResponses, stack, id, client_, server, msg, 
                            node, serverMsg, incomingMsg, msgId, clientId, 
                            client, serverSet, id_, message, msg_, head, 
                            subsets, inMsg, serverStatus_ >>

u2(self) == /\ pc[self] = "u2"
            /\ serverMsg' = [serverMsg EXCEPT ![self] = [id |-> msgId[self], serverStatus |-> serverStatus[self]]]
            /\ pc' = [pc EXCEPT ![self] = "u3"]
            /\ UNCHANGED << IDSet, status, sent, received, channels, 
                            inChannels, expectedResponses, stack, id, client_, 
                            server, msg, node, incomingMsg, msgId, clientId, 
                            serverStatus, client, serverSet, id_, message, 
                            msg_, head, subsets, inMsg, serverStatus_ >>

u3(self) == /\ pc[self] = "u3"
            /\ inChannels' = [inChannels EXCEPT ![clientId[self]] = Append((inChannels[clientId[self]]), serverMsg[self])]
            /\ pc' = [pc EXCEPT ![self] = "Error"]
            /\ UNCHANGED << IDSet, status, sent, received, channels, 
                            expectedResponses, stack, id, client_, server, msg, 
                            node, serverMsg, incomingMsg, msgId, clientId, 
                            serverStatus, client, serverSet, id_, message, 
                            msg_, head, subsets, inMsg, serverStatus_ >>

updateStatus(self) == UpdateStatus(self) \/ u1(self) \/ u2(self)
                         \/ u3(self)

GetID(self) == /\ pc[self] = "GetID"
               /\ IDSet /= <<>>
               /\ /\ IDSet' = Tail(IDSet)
                  /\ id_' = [id_ EXCEPT ![self] = Head(IDSet)]
               /\ pc' = [pc EXCEPT ![self] = "scm1"]
               /\ UNCHANGED << status, sent, received, channels, inChannels, 
                               expectedResponses, stack, id, client_, server, 
                               msg, node, serverMsg, incomingMsg, msgId, 
                               clientId, serverStatus, client, serverSet, 
                               message, msg_, head, subsets, inMsg, 
                               serverStatus_ >>

scm1(self) == /\ pc[self] = "scm1"
              /\ expectedResponses' = [expectedResponses EXCEPT ![id_[self]] = Cardinality(serverSet[self])]
              /\ pc' = [pc EXCEPT ![self] = "SendMessages"]
              /\ UNCHANGED << IDSet, status, sent, received, channels, 
                              inChannels, stack, id, client_, server, msg, 
                              node, serverMsg, incomingMsg, msgId, clientId, 
                              serverStatus, client, serverSet, id_, message, 
                              msg_, head, subsets, inMsg, serverStatus_ >>

SendMessages(self) == /\ pc[self] = "SendMessages"
                      /\ IF serverSet[self] /= {}
                            THEN /\ pc' = [pc EXCEPT ![self] = "scm2"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "Error"]
                      /\ UNCHANGED << IDSet, status, sent, received, channels, 
                                      inChannels, expectedResponses, stack, id, 
                                      client_, server, msg, node, serverMsg, 
                                      incomingMsg, msgId, clientId, 
                                      serverStatus, client, serverSet, id_, 
                                      message, msg_, head, subsets, inMsg, 
                                      serverStatus_ >>

scm2(self) == /\ pc[self] = "scm2"
              /\ \E selectedServer \in serverSet[self]:
                   /\ serverSet' = [serverSet EXCEPT ![self] = serverSet[self] \ {selectedServer}]
                   /\ /\ client_' = [client_ EXCEPT ![self] = client[self]]
                      /\ id' = [id EXCEPT ![self] = id_[self]]
                      /\ server' = [server EXCEPT ![self] = selectedServer]
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "sendClientMessage",
                                                               pc        |->  "CallLabel",
                                                               msg       |->  msg[self],
                                                               id        |->  id[self],
                                                               client_   |->  client_[self],
                                                               server    |->  server[self] ] >>
                                                           \o stack[self]]
                   /\ msg' = [msg EXCEPT ![self] = defaultInitValue]
                   /\ pc' = [pc EXCEPT ![self] = "SendClientMessage"]
              /\ UNCHANGED << IDSet, status, sent, received, channels, 
                              inChannels, expectedResponses, node, serverMsg, 
                              incomingMsg, msgId, clientId, serverStatus, 
                              client, id_, message, msg_, head, subsets, inMsg, 
                              serverStatus_ >>

CallLabel(self) == /\ pc[self] = "CallLabel"
                   /\ PrintT(client[self])
                   /\ pc' = [pc EXCEPT ![self] = "SendMessages"]
                   /\ UNCHANGED << IDSet, status, sent, received, channels, 
                                   inChannels, expectedResponses, stack, id, 
                                   client_, server, msg, node, serverMsg, 
                                   incomingMsg, msgId, clientId, serverStatus, 
                                   client, serverSet, id_, message, msg_, head, 
                                   subsets, inMsg, serverStatus_ >>

sendClientMessagesToServers(self) == GetID(self) \/ scm1(self)
                                        \/ SendMessages(self) \/ scm2(self)
                                        \/ CallLabel(self)

NodeStart(self) == /\ pc[self] = "NodeStart"
                   /\ channels[self] /= <<>>
                   /\ pc' = [pc EXCEPT ![self] = "n1"]
                   /\ UNCHANGED << IDSet, status, sent, received, channels, 
                                   inChannels, expectedResponses, stack, id, 
                                   client_, server, msg, node, serverMsg, 
                                   incomingMsg, msgId, clientId, serverStatus, 
                                   client, serverSet, id_, message, msg_, head, 
                                   subsets, inMsg, serverStatus_ >>

n1(self) == /\ pc[self] = "n1"
            /\ /\ node' = [node EXCEPT ![self] = self]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "updateStatus",
                                                        pc        |->  "NodeStart",
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
            /\ pc' = [pc EXCEPT ![self] = "UpdateStatus"]
            /\ UNCHANGED << IDSet, status, sent, received, channels, 
                            inChannels, expectedResponses, id, client_, server, 
                            msg, client, serverSet, id_, message, msg_, head, 
                            subsets, inMsg, serverStatus_ >>

nodeHandler(self) == NodeStart(self) \/ n1(self)

ClientStart(self) == /\ pc[self] = "ClientStart"
                     /\ pc' = [pc EXCEPT ![self] = "c1"]
                     /\ UNCHANGED << IDSet, status, sent, received, channels, 
                                     inChannels, expectedResponses, stack, id, 
                                     client_, server, msg, node, serverMsg, 
                                     incomingMsg, msgId, clientId, 
                                     serverStatus, client, serverSet, id_, 
                                     message, msg_, head, subsets, inMsg, 
                                     serverStatus_ >>

c1(self) == /\ pc[self] = "c1"
            /\ \/ /\ pc' = [pc EXCEPT ![self] = "SendToServer"]
               \/ /\ inChannels[self] /= <<>>
                  /\ pc' = [pc EXCEPT ![self] = "ReceiveResponse"]
            /\ UNCHANGED << IDSet, status, sent, received, channels, 
                            inChannels, expectedResponses, stack, id, client_, 
                            server, msg, node, serverMsg, incomingMsg, msgId, 
                            clientId, serverStatus, client, serverSet, id_, 
                            message, msg_, head, subsets, inMsg, serverStatus_ >>

SendToServer(self) == /\ pc[self] = "SendToServer"
                      /\ \E chosenSet \in subsets[self]:
                           /\ /\ client' = [client EXCEPT ![self] = self]
                              /\ serverSet' = [serverSet EXCEPT ![self] = chosenSet]
                              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "sendClientMessagesToServers",
                                                                       pc        |->  "ClientStart",
                                                                       id_       |->  id_[self],
                                                                       client    |->  client[self],
                                                                       serverSet |->  serverSet[self] ] >>
                                                                   \o stack[self]]
                           /\ id_' = [id_ EXCEPT ![self] = defaultInitValue]
                           /\ pc' = [pc EXCEPT ![self] = "GetID"]
                      /\ UNCHANGED << IDSet, status, sent, received, channels, 
                                      inChannels, expectedResponses, id, 
                                      client_, server, msg, node, serverMsg, 
                                      incomingMsg, msgId, clientId, 
                                      serverStatus, message, msg_, head, 
                                      subsets, inMsg, serverStatus_ >>

ReceiveResponse(self) == /\ pc[self] = "ReceiveResponse"
                         /\ inMsg' = [inMsg EXCEPT ![self] = Head((inChannels[self]))]
                         /\ inChannels' = [inChannels EXCEPT ![self] = Tail((inChannels[self]))]
                         /\ pc' = [pc EXCEPT ![self] = "c4"]
                         /\ UNCHANGED << IDSet, status, sent, received, 
                                         channels, expectedResponses, stack, 
                                         id, client_, server, msg, node, 
                                         serverMsg, incomingMsg, msgId, 
                                         clientId, serverStatus, client, 
                                         serverSet, id_, message, msg_, head, 
                                         subsets, serverStatus_ >>

c4(self) == /\ pc[self] = "c4"
            /\ expectedResponses' = [expectedResponses EXCEPT ![inMsg[self].id] = expectedResponses[inMsg[self].id] - 1]
            /\ pc' = [pc EXCEPT ![self] = "c5"]
            /\ UNCHANGED << IDSet, status, sent, received, channels, 
                            inChannels, stack, id, client_, server, msg, node, 
                            serverMsg, incomingMsg, msgId, clientId, 
                            serverStatus, client, serverSet, id_, message, 
                            msg_, head, subsets, inMsg, serverStatus_ >>

c5(self) == /\ pc[self] = "c5"
            /\ IF expectedResponses[inMsg[self].id] = 0
                  THEN /\ IDSet' = Append(IDSet, inMsg[self].id)
                  ELSE /\ TRUE
                       /\ IDSet' = IDSet
            /\ pc' = [pc EXCEPT ![self] = "c6"]
            /\ UNCHANGED << status, sent, received, channels, inChannels, 
                            expectedResponses, stack, id, client_, server, msg, 
                            node, serverMsg, incomingMsg, msgId, clientId, 
                            serverStatus, client, serverSet, id_, message, 
                            msg_, head, subsets, inMsg, serverStatus_ >>

c6(self) == /\ pc[self] = "c6"
            /\ serverStatus_' = [serverStatus_ EXCEPT ![self] = inMsg[self].serverStatus]
            /\ pc' = [pc EXCEPT ![self] = "ClientStart"]
            /\ UNCHANGED << IDSet, status, sent, received, channels, 
                            inChannels, expectedResponses, stack, id, client_, 
                            server, msg, node, serverMsg, incomingMsg, msgId, 
                            clientId, serverStatus, client, serverSet, id_, 
                            message, msg_, head, subsets, inMsg >>

clientHandler(self) == ClientStart(self) \/ c1(self) \/ SendToServer(self)
                          \/ ReceiveResponse(self) \/ c4(self) \/ c5(self)
                          \/ c6(self)

Next == (\E self \in ProcSet:  \/ sendClientMessage(self)
                               \/ updateStatus(self)
                               \/ sendClientMessagesToServers(self))
           \/ (\E self \in Nodes: nodeHandler(self))
           \/ (\E self \in Clients: clientHandler(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(nodeHandler(self)) /\ WF_vars(updateStatus(self))
        /\ \A self \in Clients : /\ WF_vars(clientHandler(self))
                                 /\ WF_vars(sendClientMessagesToServers(self))
                                 /\ WF_vars(sendClientMessage(self))

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
