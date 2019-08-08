#define PARTICIPANT_NUM 4
// Only 1 coordinator, 1 client

mtype{Active, Prepared, Committed, Aborted, VoteAbort, Failed}

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
	
	do
	:: Coordinator_state == Active ->   
		coordinatorChannelFromClient ? participantCount;
		byte i = participantCount;
		
		do		 
		:: i > 0 ->
			atomic
			{ 
			   coordinatorChannelFromParticipant ? receivedDecision, participantID;
			   if
			   :: receivedDecision == false -> finalDecision = false; i--;
			   :: else -> i--; /* This P agrees to commit*/
			   fi
			}
		:: else -> break;
		od;
		
		Coordinator_state = Prepared;
		
	:: Coordinator_state == Prepared ->		
		coordinatorChannelFromClient ? clientDecision;
		if
		:: clientDecision == 0 ->
			finalDecision = false;
		:: else -> skip;
		fi
		
		if
		:: finalDecision -> Coordinator_state = Committed;
		:: else ->  Coordinator_state = Aborted;
		fi
	
	:: Coordinator_state == Committed || Coordinator_state == Aborted ->
		clientChannelsFromCoordinator ! finalDecision; 
		i = 0;
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
			::Participant_state[id] = Prepared; coordinatorChannelFromParticipant ! true, id; 
			::Participant_state[id] = VoteAbort; coordinatorChannelFromParticipant ! false, id; 
		fi
	:: Participant_state[id] == Prepared || Participant_state[id] == VoteAbort ->
		participantChannelsFromCoordinator[id] ? finalDecision;
		assert(!(Participant_state[id] == VoteAbort && finalDecision));
		if
		:: Participant_state[id] == Prepared && finalDecision -> Participant_state[id] = Committed;
		:: else -> Participant_state[id] = Aborted;
		fi
	:: else -> break;
	od;
}

proctype failParticipant(byte id)
{
	Participant_state[id] = Failed; 
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

		//This should reset a participant(simulates a failure), and should break some invariance
		//run failParticipant(0);
	}
}

ltl client_Committed_Co {[] ( (Client_state == Committed) -> (Coordinator_state == Committed))}

ltl client_Committed_P0_involved {[] ( (Client_state == Committed && participants_involved[0] == 1) -> 
                                        ((Participant_state[0] == Committed || Participant_state[0] == Prepared) && <> (Participant_state[0] == Committed)) )}

ltl client_Committed_P0_not_involved {[] ( (Client_state == Committed && participants_involved[0] == 0) -> (Participant_state[0] != Committed) )}

ltl client_Aborted_P3_involved {[] ( (Client_state == Aborted && participants_involved[3] == 1) -> <> (Participant_state[3] == Aborted) )}

ltl P3_committed {[] ( (Participant_state[3] == Committed) -> ( Coordinator_state == Committed && Client_state != Aborted && <> (Client_state == Committed) ) )}

