#define CLIENT_NUM 3
#define PARTICIPANT_NUM 3

chan clientChannels[CLIENT_NUM] = [1] of {byte};
chan participantChannels[PARTICIPANT_NUM] = [2] of {byte, byte}; // TID, ClientId
chan coordinatorChannelC = [16] of {bool, byte}
chan coordinatorChannelP = [16] of {bool}


byte client_num = 0;
byte participant_num = 0;

proctype Coordinator(){
     bool aoc;
     byte Num_P;
    
     coordinatorChannelC ? aoc, Num_P;
     
     do
     ::if
       :: aoc == false -> printf("Abort") -> break 
       :: else /* C can get meaningful info from P's*/
       fi

       do		 
	   :: Num_P > 0 ->
			atomic
			{ 
			   coordinatorChannelP ? aoc;
			   if
               :: aoc == false -> printf("Abort") -> break 
               :: else -> Num_P--; /* This P agrees to commit*/
               fi
			}
	   :: else -> printf("Commit") -> break;
	   od;

	   break;
	od
}

proctype Client(byte id)
{
	byte i = 0;
	byte numSent = 0; 
	byte TID = _pid;
	byte receiveMsg;
	client_num++;
	
	do
	::
		do
		:: i < PARTICIPANT_NUM -> if
			::  atomic{participantChannels[i] ! TID, id ; i++; numSent++};
			::  i++;
			fi;
		:: i >= PARTICIPANT_NUM -> break;
		od;
		
        byte temp = numSent;

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

        if
          ::  coordinatorChannelC ? true, temp;
          ::  coordinatorChannelC ? false, temp;
        fi

	od;
}

proctype Participant(byte id)
{
	byte receiveTID;
	byte receiveClientId;
	participant_num++;
	do
	:: participantChannels[id] ? receiveTID, receiveClientId -> clientChannels[receiveClientId] ! receiveTID;
	od;
    
    if
          ::  coordinatorChannelP ? true;
          ::  coordinatorChannelP ? false;
    fi

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