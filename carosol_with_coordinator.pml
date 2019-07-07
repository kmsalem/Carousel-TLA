#define CLIENT_NUM 1
#define PARTICIPANT_NUM 2
// Only 1 coordinator

chan clientChannels[CLIENT_NUM] = [1] of {byte};
chan clientChannelsFromCoordinator[CLIENT_NUM] = [1] of {bool};

chan participantChannels[PARTICIPANT_NUM] = [2] of {byte, byte}; // TID, ClientId
chan participantChannelsFromCoordinator[PARTICIPANT_NUM] = [1] of {bool};

chan coordinatorChannelC = [1] of {bool, byte}
chan coordinatorChannelP = [2] of {bool}

byte client_num = 0;
byte participant_num = 0;

proctype Coordinator(){
	bool receivedDecision;
	byte participantCount;
	bool finalDecision = true;
    
	coordinatorChannelC ? receivedDecision, participantCount;
    byte temp = participantCount;
	if
	:: receivedDecision == false -> 
		finalDecision = false;
	:: else ->
		do		 
		:: participantCount > 0 ->
			atomic
			{ 
			   coordinatorChannelP ? receivedDecision;
			   if
			   :: receivedDecision == false -> atomic{finalDecision = false; break;}
			   :: else -> participantCount--; /* This P agrees to commit*/
			   fi
			}
		od;
	fi

	atomic
	{
	clientChannelsFromCoordinator[0] ! finalDecision; 
	do
	::temp > 0 -> 
		atomic{participantChannelsFromCoordinator[temp - 1] ! finalDecision; temp--;}
	::else -> 
		break;	
	od;
	}
}

proctype Client(byte id)
{
	byte i = 0;
	byte numSent = 0; 
	byte TID = _pid;
	byte receiveMsg;
	client_num++;
	bool finalDecision;

	do
	:: i < PARTICIPANT_NUM -> atomic{participantChannels[i] ! TID, id ; i++; numSent++};
	:: i >= PARTICIPANT_NUM -> break;
	od;
	
	byte temp = numSent;

	do		 
	:: numSent > 0 ->
		atomic
		{
		clientChannels[id] ? receiveMsg;
		//assert(receiveMsg == TID);
		numSent--;
		}
	:: else -> break;
	od;

	if
	  ::  coordinatorChannelC ! true, temp;
	  ::  coordinatorChannelC ! false, temp;
	fi

	participantChannelsFromCoordinator[id] ? finalDecision;
}

proctype Participant(byte id)
{
	byte receiveTID;
	byte receiveClientId;
	participant_num++;
	bool finalDecision;
	
	participantChannels[id] ? receiveTID, receiveClientId -> clientChannels[receiveClientId] ! receiveTID;
    
	if
		::coordinatorChannelP ! true;
		::coordinatorChannelP ! false;
	fi
	
	participantChannelsFromCoordinator[id] ? finalDecision;
}

init
{
	atomic
	{
		byte i = 0;
		do
		:: i < CLIENT_NUM -> run Client(i); i++;
		:: i >= CLIENT_NUM -> break;
		od;
		
		i = 0;
		
		do
		:: i < PARTICIPANT_NUM -> run Participant(i); i++;
		:: i >= PARTICIPANT_NUM -> break;
		od;
		
		run Coordinator();
	}
}

never
{
	do
	:: !(participant_num <= PARTICIPANT_NUM) -> break
	:: !(client_num <= CLIENT_NUM ) -> break
	:: else
	od
}