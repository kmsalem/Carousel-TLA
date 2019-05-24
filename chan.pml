mtype{MSG}

chan toClient = [10] of {chan}
chan getRN = [20] of {int}

/*random number generator*/
proctype Random_num (int upperbound; chan RN)
{
	int nr;
    do
    :: nr >= upperbound -> nr = 0
    :: nr < 0 -> nr=upperbound -1
    :: nr++		                                /* randomly increment */
    :: nr--		                                /* or decrement       */
    :: nr >= 0 && nr < upperbound -> RN ! nr	/* or output            */
    od;
}

/*participants*/

proctype P1(chan out)
{
    chan in = [10] of {mtype, bit};
    do
    ::bit recebit; 
	  out ! in;
      in ? MSG(recebit);
    od
}

proctype P2(chan out)
{
    chan in = [10] of {mtype, bit};
    do
    ::bit recebit; 
      out ! in;
      in ? MSG(recebit);
    od
}

proctype P3(chan out)
{
    chan in = [10] of {mtype, bit};
    do
    ::bit recebit; 
      out ! in;
      in ? MSG(recebit);
    od
}

/*Client*/

proctype Client(chan RN, in)
{
    int sSet;
    bit sendbit; 
	RN ? sSet;
	chan toSend;

    do
    ::if
      ::sSet >= 0 ->
	    in? toSend;
	    toSend ! MSG(sendbit);
	    sSet--;
	  ::else -> break;
	  fi
	od
}

/*main function*/

init{
	run Random_num (2, getRN);
	run P1(toClient);
	run P2(toClient);
	run P3(toClient);
	run Client(getRN, toClient);
}



