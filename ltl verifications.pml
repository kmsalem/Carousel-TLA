////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


int num_p_involved = 0; //global var to denote the number of participants involved

// to verify the states when client commits
int client_committed_ver; // A global var. Client will set it to be 0 at the beginning.
/* we add 1.0 to client_committed_ver when one involved participant prepares,
      add 2.0 to client_committed_ver when one involved participant commits,
      add (-3)*num_p_involved to client_committed_ver when one involved participant aborts or when a participant not involved commits.
   If client's state is Committed, then participants involved should be Prepared or Committed and eventually Committed.
   In that way, when client's state is committed, client_committed_ver >= 1* num_p_involved and eventually client_committed_ver == 3* num_p_involved*/

ltl client_v {[]((Client_state == Committed) -> ( Coordinator_state == Committed && client_committed_ver >= num_p_involved && (<> client_committed_ver == 3* num_p_involved)))}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


// If client's state is Committed, then coordinator's state can only be Committed

ltl client_Committed_Co {[] ( (Client_state == Committed) -> (Coordinator_state == Committed))}

// If client's state is Committed, then participants involved should be Prepared or Committed and eventually Committed And particpants not involved should not commit

 ltl client_Committed_P0_involved {[] ( (Client_state == Committed && participants_involved[0] == 1) -> 
                                        ((Participant_state[0] == Committed || Participant_state[0] == Prepared) && (<> Participant_state[0] == Committed)) )}
 ltl client_Committed_P0_not_involved {[] ( (Client_state == Committed && participants_involved[0] == 0) -> (Participant_state[0] != Committed) )}


 ltl client_Committed_P1_involved {[] ( (Client_state == Committed && participants_involved[1] == 1) -> 
                                        ((Participant_state[1] == Committed || Participant_state[1] == Prepared) && (<> Participant_state[1] == Committed)) )}
 ltl client_Committed_P1_not_involved {[] ( (Client_state == Committed && participants_involved[1] == 0) -> (Participant_state[1] != Committed) )}


 ltl client_Committed_P2_involved {[] ( (Client_state == Committed && participants_involved[2] == 1) -> 
                                        ((Participant_state[2] == Committed || Participant_state[2] == Prepared) && (<> Participant_state[2] == Committed)) )}
 ltl client_Committed_P2_not_involved {[] ( (Client_state == Committed && participants_involved[2] == 0) -> (Participant_state[2] != Committed) )}


 ltl client_Committed_P3_involved {[] ( (Client_state == Committed && participants_involved[3] == 1) -> 
                                        ((Participant_state[3] == Committed || Participant_state[3] == Prepared) && (<> Participant_state[3] == Committed)) )}
 ltl client_Committed_P3_not_involved {[] ( (Client_state == Committed && participants_involved[3] == 0) -> (Participant_state[3] != Committed) )}


 ltl client_Committed_P4_involved {[] ( (Client_state == Committed && participants_involved[4] == 1) -> 
                                        ((Participant_state[4] == Committed || Participant_state[4] == Prepared) && (<> Participant_state[4] == Committed)) )}
 ltl client_Committed_P4_not_involved {[] ( (Client_state == Committed && participants_involved[4] == 0) -> (Participant_state[4] != Committed) )}


 ltl client_Committed_P5_involved {[] ( (Client_state == Committed && participants_involved[5] == 1) -> 
                                        ((Participant_state[5] == Committed || Participant_state[5] == Prepared) && (<> Participant_state[5] == Committed)) )}
 ltl client_Committed_P5_not_involved {[] ( (Client_state == Committed && participants_involved[5] == 0) -> (Participant_state[5] != Committed) )} 



// If client Aborted, then participants involved will abort eventually

ltl client_Aborted_P0_involved {[] ( (Client_state == Aborted && participants_involved[0] == 1) -> ( <> Participant_state[0] == Aborted) )}
ltl client_Aborted_P1_involved {[] ( (Client_state == Aborted && participants_involved[1] == 1) -> ( <> Participant_state[1] == Aborted) )}
ltl client_Aborted_P2_involved {[] ( (Client_state == Aborted && participants_involved[2] == 1) -> ( <> Participant_state[2] == Aborted) )}
ltl client_Aborted_P3_involved {[] ( (Client_state == Aborted && participants_involved[3] == 1) -> ( <> Participant_state[3] == Aborted) )}
ltl client_Aborted_P4_involved {[] ( (Client_state == Aborted && participants_involved[4] == 1) -> ( <> Participant_state[4] == Aborted) )}
ltl client_Aborted_P5_involved {[] ( (Client_state == Aborted && participants_involved[5] == 1) -> ( <> Participant_state[5] == Aborted) )}

// If participant commits, then coordinator commits and client not in Aborted (client will eventually commit)

ltl client_Aborted_P0_involved {[] ( (Participant_state[0] == Committed) -> ( Coordinator_state == Committed && Client_state != Aborted && (<> Client_state == Committed) ) )}
ltl client_Aborted_P1_involved {[] ( (Participant_state[1] == Committed) -> ( Coordinator_state == Committed && Client_state != Aborted && (<> Client_state == Committed) ) )}
ltl client_Aborted_P2_involved {[] ( (Participant_state[2] == Committed) -> ( Coordinator_state == Committed && Client_state != Aborted && (<> Client_state == Committed) ) )}
ltl client_Aborted_P3_involved {[] ( (Participant_state[3] == Committed) -> ( Coordinator_state == Committed && Client_state != Aborted && (<> Client_state == Committed) ) )}
ltl client_Aborted_P4_involved {[] ( (Participant_state[4] == Committed) -> ( Coordinator_state == Committed && Client_state != Aborted && (<> Client_state == Committed) ) )}
ltl client_Aborted_P5_involved {[] ( (Participant_state[5] == Committed) -> ( Coordinator_state == Committed && Client_state != Aborted && (<> Client_state == Committed) ) )}
