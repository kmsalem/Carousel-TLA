#define PARTICIPANT_NUM 6
// Only 1 coordinator, 1 client

byte participant_num = 0; // the number of participants run
byte participants_involved[PARTICIPANT_NUM] = 0; // when the ith participant received a message,  participant_involved[i] will be set to 1.

/* All proc's will start with Active.
      Coordinator: will get message from Client  
*/
mtype{Active, Prepared, Committed, Aborted}
mtype Coordinator_state;
mtype Client_state;
mtype Participant_state [6];

chan clientChannelsFromParticipant = [1] of {byte};
chan clientChannelsFromCoordinator = [1] of {bool};

chan participantChannelsFromClient[PARTICIPANT_NUM] = [2] of {byte}; // TID
chan participantChannelsFromCoordinator[PARTICIPANT_NUM] = [1] of {bool};

chan coordinatorChannelFromClient = [1] of {byte} // first time read: participant count; second time read: commit/abort
chan coordinatorChannelFromParticipant = [2] of {bool, byte} // decision, ID



active proctype Coordinator(){
	byte clientDecision;
	bool receivedDecision;

	Coordinator_state = Active;
	bool finalDecision = true;
	byte participantCount;
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

	if
	::Coordinator_state == Active -> Coordinator_state = Committed;
	fi

	i = 0;
	
	clientChannelsFromCoordinator ! finalDecision;
	do
	::i < PARTICIPANT_NUM -> 
		if
		:: participants[i] && participants_involved[i] == 1-> participantChannelsFromCoordinator[i] ! finalDecision;
		fi
		i++;
	::else -> 
		break;	
	od;

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
	  ::  coordinatorChannelFromClient ! 0;                         // In this case, the client's state is Active, which means it agrees to commit. 
	  ::  Client_state = Aborted; coordinatorChannelFromClient ! 1; // The client's state is Aborted here. (disagree to commit)
	fi

	clientChannelsFromCoordinator ? finalDecision;

	// if this line is reached, the final decision has already made by coordinator  

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
	
	Participant_state [id] = Active;

	participantChannelsFromClient[id] ? receiveTID -> clientChannelsFromParticipant ! receiveTID;
	participants_involved[id] = 1; // if this line is reached, the participant is involved in the transaction
    
    // update state and notify the coordinator
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

