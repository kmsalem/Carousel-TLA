------------------------------- MODULE carousel -------------------------------

(***************************************************************************)
(* This is a TLA+ specification of the Carousel protocol.                  *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets, Sequences, TLC
CONSTANT C, N, T, NumOfMessages

ASSUME C \in Nat /\ C > 0
ASSUME N \in Nat /\ N > 0
Clients == 1..C
Nodes == 1..N

(* --algorithm progress
variable
  IDSet = <<1..T>>,
  \* Status of each node
  status = [n \in Nodes |-> "Init"],
  
  sent = [n \in Nodes |-> 0],
  received = [n \in Nodes |-> 0],
  channels = [n \in Nodes |-> <<>>],

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


\* Client
procedure createClientMsg(msg, client)
variable
    tmp;
begin
  P1:
\*    Get ID from IDSet and remove it from IDSet
    await IDSet # <<>>;  \* First check if IDSet is empty, if not, wait
    tmp := Head(IDSet);
    print tmp;
    print IDSet;
    IDSet := Tail(IDSet);
    msg := [id |-> tmp, client |-> client];
end procedure


procedure createServerMsg(msg, id, serverStatus)
begin
  P1:
\*    Put ID back to IDSet
    IDSet := Append(IDSet, id);
    msg := [id |-> id, serverStatus |-> serverStatus];
end procedure


\* Appends status to the progress set at Quorum nodes
\*procedure updateStatus(node)
\*variable 
\*    incoming = "";
\*begin
\*  P1:
\*    recv(channels[node], incoming);
\*  IncrementReceived:
\*    received[node] := received[node] + 1;
\*  Update:
\*    status[node] := incoming;
\*end procedure
\*
\*
\*procedure updateCounter(node)
\*variable 
\*    incoming = "";
\*begin
\*  P1:
\*    recv(channels[node], incoming);
\*    status[node] := incoming;
\*end procedure


\*procedure sendServerMessages(msg)
\*variable 
\*    incoming = ""; 
\*    toSend;
\*begin
\*  P0:
\*    serverSet := msg.serverSet;
\*  P1:
\*    while counter < NumOfMessages do
\*        with s \in serverSet do
\*            send(channels[s], "test");
\*            sent[client] := sent[client] + 1;
\*        end with;
\*    IncrementCounter:
\*        counter := counter + 1;
\*    end while;
\*end procedure


procedure sendClientMessagesToServers(client, serverSet)
variable 
    msg;
begin
  P0:
\*    while serverSet # {} do
\*        with selectedServer \in serverSet do
\*\*            Removed selected from serverSet
\*            serverSet := serverSet \ {selectedServer};
\*\*            call createClientMsg(msg, client);
\*        end with;
\*    end while;
    print serverSet;
end procedure

process sendClientMessages \in Clients
variables
    msg,
    head,
    subsets = SUBSET Nodes;
begin
    P0:
        with chosen \in subsets do
\*            call sendClientMessagesToServers(self, chosen);
            print chosen;
        end with;
end process;


\*fair process nodeHandler \in Nodes
\*variable
\*  message = "";
\*begin
\*  test:
\*  await channels[self] # <<>>;
\*  call updateStatus(self);
\*
\*end process;

end algorithm *)
\* BEGIN TRANSLATION
\* Label P1 of procedure createClientMsg at line 46 col 5 changed to P1_
\* Label P0 of procedure sendClientMessagesToServers at line 119 col 5 changed to P0_
\* Process variable msg of process sendClientMessages at line 124 col 5 changed to msg_
\* Procedure variable msg of procedure sendClientMessagesToServers at line 109 col 5 changed to msg_s
\* Parameter msg of procedure createClientMsg at line 40 col 27 changed to msg_c
\* Parameter client of procedure createClientMsg at line 40 col 32 changed to client_
CONSTANT defaultInitValue
VARIABLES IDSet, status, sent, received, channels, pc, stack, msg_c, client_, 
          tmp, msg, id, serverStatus, client, serverSet, msg_s, msg_, head, 
          subsets

vars == << IDSet, status, sent, received, channels, pc, stack, msg_c, client_, 
           tmp, msg, id, serverStatus, client, serverSet, msg_s, msg_, head, 
           subsets >>

ProcSet == (Clients)

Init == (* Global variables *)
        /\ IDSet = <<1..T>>
        /\ status = [n \in Nodes |-> "Init"]
        /\ sent = [n \in Nodes |-> 0]
        /\ received = [n \in Nodes |-> 0]
        /\ channels = [n \in Nodes |-> <<>>]
        (* Procedure createClientMsg *)
        /\ msg_c = [ self \in ProcSet |-> defaultInitValue]
        /\ client_ = [ self \in ProcSet |-> defaultInitValue]
        /\ tmp = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure createServerMsg *)
        /\ msg = [ self \in ProcSet |-> defaultInitValue]
        /\ id = [ self \in ProcSet |-> defaultInitValue]
        /\ serverStatus = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure sendClientMessagesToServers *)
        /\ client = [ self \in ProcSet |-> defaultInitValue]
        /\ serverSet = [ self \in ProcSet |-> defaultInitValue]
        /\ msg_s = [ self \in ProcSet |-> defaultInitValue]
        (* Process sendClientMessages *)
        /\ msg_ = [self \in Clients |-> defaultInitValue]
        /\ head = [self \in Clients |-> defaultInitValue]
        /\ subsets = [self \in Clients |-> SUBSET Nodes]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "P0"]

P1_(self) == /\ pc[self] = "P1_"
             /\ IDSet # <<>>
             /\ tmp' = [tmp EXCEPT ![self] = Head(IDSet)]
             /\ PrintT(tmp'[self])
             /\ PrintT(IDSet)
             /\ IDSet' = Tail(IDSet)
             /\ msg_c' = [msg_c EXCEPT ![self] = [id |-> tmp'[self], client |-> client_[self]]]
             /\ pc' = [pc EXCEPT ![self] = "Error"]
             /\ UNCHANGED << status, sent, received, channels, stack, client_, 
                             msg, id, serverStatus, client, serverSet, msg_s, 
                             msg_, head, subsets >>

createClientMsg(self) == P1_(self)

P1(self) == /\ pc[self] = "P1"
            /\ IDSet' = Append(IDSet, id[self])
            /\ msg' = [msg EXCEPT ![self] = [id |-> id[self], serverStatus |-> serverStatus[self]]]
            /\ pc' = [pc EXCEPT ![self] = "Error"]
            /\ UNCHANGED << status, sent, received, channels, stack, msg_c, 
                            client_, tmp, id, serverStatus, client, serverSet, 
                            msg_s, msg_, head, subsets >>

createServerMsg(self) == P1(self)

P0_(self) == /\ pc[self] = "P0_"
             /\ PrintT(serverSet[self])
             /\ pc' = [pc EXCEPT ![self] = "Error"]
             /\ UNCHANGED << IDSet, status, sent, received, channels, stack, 
                             msg_c, client_, tmp, msg, id, serverStatus, 
                             client, serverSet, msg_s, msg_, head, subsets >>

sendClientMessagesToServers(self) == P0_(self)

P0(self) == /\ pc[self] = "P0"
            /\ \E chosen \in subsets[self]:
                 PrintT(chosen)
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << IDSet, status, sent, received, channels, stack, 
                            msg_c, client_, tmp, msg, id, serverStatus, client, 
                            serverSet, msg_s, msg_, head, subsets >>

sendClientMessages(self) == P0(self)

Next == (\E self \in ProcSet:  \/ createClientMsg(self)
                               \/ createServerMsg(self)
                               \/ sendClientMessagesToServers(self))
           \/ (\E self \in Clients: sendClientMessages(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

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
