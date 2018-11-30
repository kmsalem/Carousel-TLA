------------------------------- MODULE carousel -------------------------------

(***************************************************************************)
(* This is a TLA+ specification of the Carousel protocol.                  *)
(***************************************************************************)

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
\*    await IDSet /= <<>>;  \* First check if IDSet is empty, if not, wait
    id := Head(IDSet);
    IDSet := Tail(IDSet);
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
\*      while TRUE do
        with chosen \in subsets do
            call sendClientMessagesToServers(self, chosen);
        end with;
\*      end while;
end process;


\*fair process nodeHandler \in Nodes
\*variable
\*  message = "";
\*begin
\*  nodeHandler:
\*    while TRUE do
\*      await channels[self] /= <<>>;
\*      call updateStatus(self);
\*    end while;
\*end process;
\*
\*
\*fair process clientHandler \in Clients
\*variable
\*  inMsg,
\*  serverStatus;
\*begin
\*  clientHandler:
\*    while TRUE do
\*      await inChannels[self] /= <<>>;
\*      recv(inChannels[self], inMsg);
\*      
\*\*      Recycle ID
\*      IDSet := Append(IDSet, inMsg.id);
\*      serverStatus := inMsg.serverStatus;
\*\*      Assert serverStatus = status[server];
\*    end while;
\*end process;

end algorithm *)
\* BEGIN TRANSLATION
\* Label P1 of procedure sendClientMessage at line 45 col 5 changed to P1_
\* Label sendClientMessages of process sendClientMessages at line 108 col 9 changed to sendClientMessages_
\* Process variable msg of process sendClientMessages at line 102 col 5 changed to msg_
\* Procedure variable id of procedure sendClientMessagesToServers at line 82 col 5 changed to id_
\* Parameter client of procedure sendClientMessage at line 40 col 33 changed to client_
CONSTANT defaultInitValue
VARIABLES IDSet, status, sent, received, channels, inChannels, pc, stack, id, 
          client_, server, msg, node, serverMsg, incomingMsg, msgId, clientId, 
          serverStatus, client, serverSet, id_, msg_, head, subsets

vars == << IDSet, status, sent, received, channels, inChannels, pc, stack, id, 
           client_, server, msg, node, serverMsg, incomingMsg, msgId, 
           clientId, serverStatus, client, serverSet, id_, msg_, head, 
           subsets >>

ProcSet == (Clients)

Init == (* Global variables *)
        /\ IDSet = <<1,2,3,4,5,6,7,8>>
        /\ status = [n \in Nodes |-> "Init"]
        /\ sent = [n \in Nodes |-> 0]
        /\ received = [n \in Nodes |-> 0]
        /\ channels = [n \in Nodes |-> <<>>]
        /\ inChannels = [c \in Clients |-> <<>>]
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
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "sendClientMessages_"]

P1_(self) == /\ pc[self] = "P1_"
             /\ msg' = [msg EXCEPT ![self] = [id |-> id[self], client |-> client_[self]]]
             /\ channels' = [channels EXCEPT ![server[self]] = Append((channels[server[self]]), msg'[self])]
             /\ sent' = [sent EXCEPT ![server[self]] = sent[server[self]] + 1]
             /\ pc' = [pc EXCEPT ![self] = "Error"]
             /\ UNCHANGED << IDSet, status, received, inChannels, stack, id, 
                             client_, server, node, serverMsg, incomingMsg, 
                             msgId, clientId, serverStatus, client, serverSet, 
                             id_, msg_, head, subsets >>

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
            /\ UNCHANGED << IDSet, sent, stack, id, client_, server, msg, node, 
                            client, serverSet, id_, msg_, head, subsets >>

updateStatus(self) == P1(self)

GetID(self) == /\ pc[self] = "GetID"
               /\ id_' = [id_ EXCEPT ![self] = Head(IDSet)]
               /\ IDSet' = Tail(IDSet)
               /\ pc' = [pc EXCEPT ![self] = "SendMessages"]
               /\ UNCHANGED << status, sent, received, channels, inChannels, 
                               stack, id, client_, server, msg, node, 
                               serverMsg, incomingMsg, msgId, clientId, 
                               serverStatus, client, serverSet, msg_, head, 
                               subsets >>

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
                                      inChannels, node, serverMsg, incomingMsg, 
                                      msgId, clientId, serverStatus, client, 
                                      id_, msg_, head, subsets >>

sendClientMessagesToServers(self) == GetID(self) \/ SendMessages(self)

sendClientMessages_(self) == /\ pc[self] = "sendClientMessages_"
                             /\ \E chosen \in subsets[self]:
                                  /\ /\ client' = [client EXCEPT ![self] = self]
                                     /\ serverSet' = [serverSet EXCEPT ![self] = chosen]
                                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "sendClientMessagesToServers",
                                                                              pc        |->  "Done",
                                                                              id_       |->  id_[self],
                                                                              client    |->  client[self],
                                                                              serverSet |->  serverSet[self] ] >>
                                                                          \o stack[self]]
                                  /\ id_' = [id_ EXCEPT ![self] = defaultInitValue]
                                  /\ pc' = [pc EXCEPT ![self] = "GetID"]
                             /\ UNCHANGED << IDSet, status, sent, received, 
                                             channels, inChannels, id, client_, 
                                             server, msg, node, serverMsg, 
                                             incomingMsg, msgId, clientId, 
                                             serverStatus, msg_, head, subsets >>

sendClientMessages(self) == sendClientMessages_(self)

Next == (\E self \in ProcSet:  \/ sendClientMessage(self)
                               \/ updateStatus(self)
                               \/ sendClientMessagesToServers(self))
           \/ (\E self \in Clients: sendClientMessages(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Clients : /\ WF_vars(sendClientMessages(self))
                                 /\ WF_vars(sendClientMessagesToServers(self))
                                 /\ WF_vars(sendClientMessage(self))

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
