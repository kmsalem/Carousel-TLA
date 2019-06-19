#define CLIENT_NUM 2
#define PARTICIPANT_NUM 2


chan clientChannels[CLIENT_NUM] = [1] of {byte};
chan participantChannels[PARTICIPANT_NUM] = [2] of {byte, byte}; // TID, ClientId
byte client_ids = 0;
byte participant_ids = 0;

init
{
	assert(1 == 1)
}

active [CLIENT_NUM] proctype Client()
{
                byte id = 0;
	atomic{ id = client_ids; client_ids++; }

	byte i = 0;
	byte numSent = 0; 
	byte TID = _pid;
	byte receiveMsg;
	do
	::
		// Re-initialize the local variables
		i = 0;
		numSent = 0;

		do
		:: i < PARTICIPANT_NUM -> atomic{participantChannels[i] ! TID, id ; i++; numSent++;}
		:: i >= PARTICIPANT_NUM -> break;
		od;
		
		assert(numSent == PARTICIPANT_NUM)

		do		 
		:: numSent > 0 ->
			atomic
			{
			clientChannels[id] ? receiveMsg;
			assert(receiveMsg == TID);
			numSent--;
			}
		:: else -> break;
		od;
	od;
}

active [PARTICIPANT_NUM] proctype Participant()
{
                byte id = 0;
	atomic{ id = participant_ids; participant_ids++; }
	byte receiveTID;
	byte receiveClientId;
	do
	:: participantChannels[id] ? receiveTID, receiveClientId -> clientChannels[receiveClientId] ! receiveTID;id++;
	od;
}


