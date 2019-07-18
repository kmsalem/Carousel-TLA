#define PARTICIPANT_NUM 6
// Only 1 coordinator, 1 client

byte participant_num = 0; // the number of participants run
byte participants_involved[PARTICIPANT_NUM] = 0; // when the ith participant received a message,  participant_involved[i] will be set to 1.

/* All proc's will start with Active.
      Coordinator: will get message from Client  
*/
mtype{Active, Committed, Aborted}
mtype Coordinator_state;
mtype Client_state;
mtype Participant_state [6];

chan clientChannelsFromParticipant = [1] of {byte};
chan clientChannelsFromCoordinator = [1] of {mtype};

chan participantChannelsFromClient[PARTICIPANT_NUM] = [2] of {byte}; // TID
chan participantChannelsFromCoordinator[PARTICIPANT_NUM] = [1] of {mtype};

// first time read form this channel: participant count; If second time read succeeds, the client's state is available to check.
chan coordinatorChannelFromClient = [1] of {byte}
// Coordinator will read ID of the ith participant form this channel. If read succeeds, the ith participant's state is available to check.  
chan coordinatorChannelFromParticipant = [2] of {byte} 


active proctype Coordinator(){
	byte clientDecision;

	Coordinator_state = Active;
	
	byte participantCount;
	bool participants[PARTICIPANT_NUM];
	byte participantID;
    
	coordinatorChannelFromClient ? participantCount;
    byte i = participantCount;
	
	do		 
	:: i > 0 ->
		atomic
		{ 
		   coordinatorChannelFromParticipant ? participantID;
		   // if this line is reached, the participant, whose ID is participantID, has updated its state
		   if
		   :: Participant_state[participantID] == Aborted -> Coordinator_state = Aborted; i--;
		   :: else -> i--; participants[participantID] = true; /* This P agrees to commit*/
		   fi
		}
	:: else -> break;
	od;

	coordinatorChannelFromClient ? clientDecision;
    // if this line is reached, Client has already made a decision
	if
	::  Client_state == Aborted ->
		 Coordinator_state = Aborted;
	fi

	if
	::Coordinator_state == Active -> Coordinator_state = Committed;
	fi

	i = 0;
	
	clientChannelsFromCoordinator ! Coordinator_state; 
	do
	::i < PARTICIPANT_NUM -> 
		if
		:: participants[i] -> participantChannelsFromCoordinator[i] ! Coordinator_state;
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
	mtype finalDecision;

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

    // notify Coordinator
	if
	  ::  coordinatorChannelFromClient ! 0;                         // In this case, the client's state is Active, which means it agrees to commit. 
	  ::  Client_state = Aborted; coordinatorChannelFromClient ! 1; // The client's state is Aborted here. (disagree to commit)
	fi

	clientChannelsFromCoordinator ? finalDecision;
	// if this line is reached, the final decision has already made by coordinator    
	if
	  :: Coordinator_state  == Committed -> Client_state = Committed;
     	 :: else -> Client_state = Aborted;
    fi

}

proctype Participant(byte id)
{
	byte receiveTID;
	byte receiveClientId;
	participant_num++;
	mtype finalDecision;
	
	Participant_state [id] = Active;

	participantChannelsFromClient[id] ? receiveTID -> clientChannelsFromParticipant ! receiveTID;
	participants_involved[id] = 1; // if this line is reached, the participant is involved in the transaction
    
    // update state and notify the coordinator
	if
		::coordinatorChannelFromParticipant ! id;                                    // In this case, the participant's state is Active, which means it agrees to commit. 
		::Participant_state[id] = Aborted -> coordinatorChannelFromParticipant ! id; // The participant's state is Aborted here. (disagree to commit)
	fi

	participantChannelsFromCoordinator[id] ? finalDecision;

    if
	  :: Coordinator_state == Committed -> Participant_state[id] = Committed;
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

// flag and index is declared for verifications in never, since it seems we are not able to declare local vars in never
flag = true;
int i = 0;

never
{
	do
	
    /* If Client_state is committed, coordinator should not be Aborted and no participant involved should be Aborted. (Also, participant not involved should not be  
	      committed)*/
	:: if 	
	   ::  Client_state == Committed &&  Coordinator_state == Aborted -> break;
	   ::  Client_state == Committed && Coordinator_state == Committed -> i = 0;
	              do
	              :: i < PARTICIPANT_NUM -> 
	                    if
	                    :: participants_involved[i] == 1 && Participant_state[i] == Aborted -> flag = false;break;
                        :: participants_involved[i] == 0 && Participant_state[i] == Committed -> flag = false;break;
                        :: else -> i++;
                        fi
	              :: i >= PARTICIPANT_NUM -> break;
	              od;
	              if
	              ::flag == false -> break;
	              ::else
	              fi
	    ::  else
	    fi

	/* If any participant_state is committed, then coordinator_state should be committed and client_state can not be aborted
	:: i = 0;
	   do
	        :: i < PARTICIPANT_NUM -> 
	                    if
	                    :: participants_involved[i] == 1 && Participant_state[i] == Committed && (Coordinator_state != Commited || Client_state == Aborted)-> 
	                                            flag = false;break;
                        :: else -> i++;
                        fi
	        :: i >= PARTICIPANT_NUM -> break;
	    od;
	    if
	        ::flag == false -> break;
	        ::else
	    fi
    
    ::
	od
}