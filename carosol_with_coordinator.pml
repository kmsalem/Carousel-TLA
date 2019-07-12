#define PARTICIPANT_NUM 6
// Only 1 coordinator, 1 client

mtype{Active, Prepared, Committed, Aborted}

chan clientChannelsFromParticipant = [1] of {byte};
chan clientChannelsFromCoordinator = [1] of {bool};

chan participantChannelsFromClient[PARTICIPANT_NUM] = [2] of {byte}; // TID
chan participantChannelsFromCoordinator[PARTICIPANT_NUM] = [1] of {bool};

chan coordinatorChannelFromClient = [1] of {byte} // first time read: participant count; second time read: commit/abort
chan coordinatorChannelFromParticipant = [2] of {bool, byte} // decision, ID

byte participant_num = 0;

mtype Coordinator_state = Active;
mtype Client_state = Active;
mtype Participant_state [6] = Active;

active proctype Coordinator(){
	bool receivedDecision;
	byte clientDecision;
	
	byte participantCount;
	bool finalDecision = true;
	bool participants[PARTICIPANT_NUM];
	byte participantID;
    
	coordinatorChannelFromClient ? participantCount;
    byte i = participantCount;
	
	do		 
	:: i > 0 ->
		atomic
		{ 
		   coordinatorChannelFromParticipant ? receivedDecision, participantID;
		   if
		   :: receivedDecision == false -> finalDecision = false; Coordinator_state = Aborted; i--;
		   :: else -> i--; participants[participantID] = true; /* This P agrees to commit*/
		   fi
		}
	:: else -> break;
	od;

	coordinatorChannelFromClient ? clientDecision;
	if
	:: clientDecision == 0 ->
		finalDecision = false; Coordinator_state = Aborted;
	fi

	i = 0;
	
	clientChannelsFromCoordinator ! finalDecision; 
	do
	::i < PARTICIPANT_NUM -> 
		if
		:: participants[i] -> participantChannelsFromCoordinator[i] ! finalDecision;
		fi
		i++;
	::else -> 
		break;	
	od;

	if
	::Coordinator_state == Active -> Coordinator_state = Committed;
	fi

}

active proctype Client()
{
	byte i = 0;
	byte numSent = 0; 
	byte TID = _pid;
	byte receiveMsg;
	bool finalDecision;

	do
	:: i < PARTICIPANT_NUM -> if
		:: participantChannelsFromClient[i] ! TID; i++; numSent++;
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
	  ::  coordinatorChannelFromClient ! 1; Client_state = Prepared;
	  ::  coordinatorChannelFromClient ! 0; Client_state = Aborted;
	fi

	clientChannelsFromCoordinator ? finalDecision;

	if
	  :: Client_state == Prepared && finalDecision-> Client_state = Committed;
     	 :: else -> Client_state = Aborted;
    fi

}

proctype Participant(byte id)
{
	byte receiveTID;
	byte receiveClientId;
	participant_num++;
	bool finalDecision;
	assert(Participant_state[id] == Active);

	participantChannelsFromClient[id] ? receiveTID -> clientChannelsFromParticipant ! receiveTID;
    
	if
		::coordinatorChannelFromParticipant ! true, id; Participant_state[id] = Prepared;
		::coordinatorChannelFromParticipant ! false, id; Participant_state[id] = Aborted;
	fi
	
	participantChannelsFromCoordinator[id] ? finalDecision;

    if
	  :: Participant_state[id] == Prepared && finalDecision-> Participant_state[id] = Committed;
     	 :: else -> Participant_state[id] = Aborted;
    fi

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
	
	:: if 
	   :: Client_state == Committed ->  Coordinator_state != Committed -> break
	   :: Participant_state[0] == Committed ->  Coordinator_state != Committed -> break
	   :: Participant_state[1] == Committed ->  Coordinator_state != Committed -> break
	   :: Participant_state[2] == Committed ->  Coordinator_state != Committed -> break
	   :: Participant_state[3] == Committed ->  Coordinator_state != Committed -> break
	   :: Participant_state[4] == Committed ->  Coordinator_state != Committed -> break
	   :: Participant_state[5] == Committed ->  Coordinator_state != Committed -> break
	   :: else
	   fi

	:: else
	od
}