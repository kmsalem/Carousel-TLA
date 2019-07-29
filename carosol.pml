#define PARTICIPANT_NUM 4
// Only 1 coordinator, 1 client

mtype{Active, Prepared, Committed, Aborted}

chan clientChannelsFromParticipant = [1] of {byte};
chan clientChannelsFromCoordinator = [1] of {bool};

chan participantChannelsFromClient[PARTICIPANT_NUM] = [2] of {byte}; // TID
chan participantChannelsFromCoordinator[PARTICIPANT_NUM] = [1] of {bool};

chan coordinatorChannelFromClient = [1] of {byte} // first time read: participant count; second time read: commit/abort
chan coordinatorChannelFromParticipant = [2] of {bool, byte} // decision, ID

byte participant_num = 0;

mtype Coordinator_state;
mtype Client_state;
mtype Participant_state[PARTICIPANT_NUM];

byte participants_involved[PARTICIPANT_NUM] = 0; // when the ith participant received a message,  participant_involved[i] will be set to 1.

active proctype Coordinator(){
	bool receivedDecision;
	byte clientDecision;
	
	byte participantCount;
	bool finalDecision = true;
	byte participantID;

	Coordinator_state = Active;
    
	coordinatorChannelFromClient ? participantCount;
    byte i = participantCount;
	
	do		 
	:: i > 0 ->
		atomic
		{ 
		   coordinatorChannelFromParticipant ? receivedDecision, participantID;
		   if
		   :: receivedDecision == false -> finalDecision = false; Coordinator_state = Aborted; i--;
		   :: else -> i--; /* This P agrees to commit*/
		   fi
		}
	:: else -> break;
	od;

	coordinatorChannelFromClient ? clientDecision;
	if
	:: clientDecision == 0 ->
		finalDecision = false; Coordinator_state = Aborted;
	:: else -> skip;
	fi

	i = 0;
	
	clientChannelsFromCoordinator ! finalDecision; 
	do
	::i < PARTICIPANT_NUM -> 
		if
		:: participants_involved[i] -> participantChannelsFromCoordinator[i] ! finalDecision;
		:: else -> skip;
		fi
		i++;
	::else -> 
		break;	
	od;

	if
	::Coordinator_state == Active -> Coordinator_state = Committed;
	::else -> skip;
	fi

}

active proctype Client()
{
	byte i = 0;
	byte numSent = 0; 
	byte TID = _pid;
	byte receiveMsg;
	bool finalDecision;

   	 Client_state = Active;

	do
	:: i < PARTICIPANT_NUM -> 
	    if
		:: participantChannelsFromClient[i] ! TID;participants_involved[i] = 1; i++; numSent++;
		:: i++;
		fi
	:: i >= PARTICIPANT_NUM -> break;
	od;
	
	coordinatorChannelFromClient ! numSent;
	
	byte temp = numSent;

	do		 
	:: numSent > 0 ->
		clientChannelsFromParticipant ? receiveMsg;
		assert(receiveMsg == TID);
		numSent--;
	:: else -> break;
	od;

	if
	  ::  coordinatorChannelFromClient ! 1;
	  ::  coordinatorChannelFromClient ! 0; Client_state = Aborted;
	fi

	clientChannelsFromCoordinator ? finalDecision;

	if
	  :: Client_state == Active && finalDecision-> Client_state = Committed;
      :: else -> Client_state = Aborted;
    fi

}

proctype Participant(byte id)
{
	byte receiveTID;
	byte receiveClientId;
	participant_num++;
	bool finalDecision;

	Participant_state[id] = Active;
	
	do
	:: Participant_state[id] == Active ->
		participantChannelsFromClient[id] ? receiveTID;
		clientChannelsFromParticipant ! receiveTID;
		if
			::coordinatorChannelFromParticipant ! true, id; Participant_state[id] = Prepared;
			::coordinatorChannelFromParticipant ! false, id; Participant_state[id] = Aborted;
		fi
	:: Participant_state[id] == Prepared || Participant_state[id] == Aborted ->
		participantChannelsFromCoordinator[id] ? finalDecision;
		if
		  :: Participant_state[id] == Prepared && finalDecision-> Participant_state[id] = Committed; break;
		  :: else -> Participant_state[id] = Aborted; break;
		fi
	od;
}

init
{
	atomic
	{
		byte i = 0;
		
		do
		:: i < PARTICIPANT_NUM -> run Participant(i); i++;
		:: i >= PARTICIPANT_NUM -> break;
		od;
	}
}

never
{
	do
	:: !(participant_num <= PARTICIPANT_NUM) -> break
	:: else
	od
}
