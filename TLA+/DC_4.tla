------------------------------- MODULE DC_mx -------------------------------

EXTENDS Integers, TLC, ModExp

VARIABLES a0, a1, a2, a3, g, key, x0, x1, x2, x3, h0, h1, h2, h3, ck0, ck1, ck2, ck3, pc, p

vars == << a0, a1, a2, a3, g, key, x0, x1, x2, x3, h0, h1, h2, h3, ck0, ck1, ck2, ck3, pc, p >>

Init == (* Global variables *)
        /\ a0 \in Nat       (* Secret exponent of S0 *)
        /\ a1 \in Nat       (* Secret exponent of S1 *)
        /\ a2 \in Nat       (* Secret exponent of S2 *)
        /\ a3 \in Nat       (* Secret exponent of S3 *)
        /\ p = 13           (* Finite field size *)
        /\ g = 2            (* Generator of Fp *)
        /\ key = mod_exp(a3,mod_exp(a2,mod_exp(a1,mod_exp(a0,g,1,p),1,p),1,p),1,p) (* Shared key *)
        /\ x0 = 0           (* Value computed by S0 *)
        /\ x1 = 0           (* Value computed by S1 *)
        /\ x2 = 0           (* Value computed by S2 *)
        /\ x3 = 0           (* Value computed by S3 *)
        /\ h0 = 0           (* Number of message received by S0 *)
        /\ h1 = 0           (* Number of message received by S1 *)
        /\ h2 = 0           (* Number of message received by S2 *)
        /\ h3 = 0           (* Number of message received by S3 *)
        /\ ck0 = FALSE      (* Boolean to indicate that S0 has received the common key *)
        /\ ck1 = FALSE      (* Boolean to indicate that S1 has received the common key *)
        /\ ck2 = FALSE      (* Boolean to indicate that S2 has received the common key *)
        /\ ck3 = FALSE      (* Boolean to indicate that S3 has received the common key *)
        /\ pc = "Phase 1"
        
Phase1 == /\ pc = "Phase 1"
          /\ x0' = mod_exp(a0,g,1,p)                 (* S0 calculates x0 = g ^ a0 mod p, sends it to S1 *)    
          /\ x2' = mod_exp(a2,g,1,p)                 (* S2 calculates x2 = g ^ a2 mod p, sends it to S3 *)
          /\ h1' = h1 + 1                            (* S1 receives x0, h1 increases *)
          /\ x1' = mod_exp(a1,x0',1,p)               (* S1 calculates x1 = x0 ^ a1 mod p, sends it to S2 and S3 *)
          /\ h3' = h3 + 1                            (* S3 receives x2, h3 increases *)
          /\ x3' = mod_exp(a3,x2',1,p)               (* S3 calculates x3 = x2 ^ a3 mod p, sends it to S0 and S1 *)
          /\ IF x0' = key /\ h0 = 2                  (* If the value of x0 equals key and S0 has received two *)
                 THEN /\ ck0' = TRUE                 (* messages, then ck0 becomes TRUE *)
                 ELSE /\ ck0' = ck0
                      
          /\ IF x1' = key /\ h1' = 3                 (* If the value of x1 equals key and S1 has received three *)
                 THEN /\ ck1' = TRUE                 (* messages, then ck1 becomes TRUE *)
                 ELSE /\ ck1' = ck1
                      
          /\ IF x2' = key /\ h2 = 2                  (* If the value of x2 equals key and S2 has received two *)
                 THEN /\ ck2' = TRUE                 (* messages, then ck2 becomes TRUE *)
                 ELSE /\ ck2' = ck2
                      
          /\ IF x3' = key /\ h3' = 3                 (* If the value of x3 equals key and S3 has received three *)
                 THEN /\ ck3' = TRUE                 (* messages, then ck3 becomes TRUE *)
                 ELSE /\ ck3' = ck3
                     
          /\ pc' = "Phase 2"                         (* Phase 1 ends, starts Phase 2 *)
          /\ UNCHANGED << a0, a1, a2, a3, key, g, p, h0, h2 >>   (* The value of these variables are unchanged *)
         
Phase2 == /\ pc = "Phase 2"
          /\ h0' = h0 + 1                            (* S0 receives x3, h0 increases *)
          /\ h1' = h1 + 1                            (* S1 receives x3, h1 increases *)
          /\ h2' = h2 + 1                            (* S2 receives x1, h2 increases *)
          /\ h3' = h3 + 1                            (* S3 receives x1, h3 increases *)
          /\ x0' = mod_exp(a0,x3,1,p)                (* S0 calculates x0 = x3 ^ a0 mod p, sends it to S1 *)
          /\ x1' = mod_exp(a1,x3,1,p)                (* S1 calculates x1 = x3 ^ a1 mod p, sends it to S0 *)
          /\ x2' = mod_exp(a2,x1,1,p)                (* S2 calculates x2 = x1 ^ a2 mod p, sends it to S3 *)
          /\ x3' = mod_exp(a3,x1,1,p)                (* S3 calculates x3 = x1 ^ a3 mod p, sends it to S2 *)
          /\ IF x0' = key /\ h0' = 2                 (* If the value of x0 equals key and S0 has received two *)
                 THEN /\ ck0' = TRUE                 (* messages, then ck0 becomes TRUE *)
                 ELSE /\ ck0' = ck0
                      
          /\ IF x1' = key /\ h1' = 3                 (* If the value of x1 equals key and S1 has received three *)
                 THEN /\ ck1' = TRUE                 (* messages, then ck1 becomes TRUE *)
                 ELSE /\ ck1' = ck1
                      
          /\ IF x2' = key /\ h2' = 2                 (* If the value of x2 equals key and S2 has received two *)
                 THEN /\ ck2' = TRUE                 (* messages, then ck2 becomes TRUE *)
                 ELSE /\ ck2' = ck2
                      
          /\ IF x3' = key /\ h3' = 3                 (* If the value of x3 equals key and S3 has received three *)
                 THEN /\ ck3' = TRUE                 (* messages, then ck3 becomes TRUE *)
                 ELSE /\ ck3' = ck3
          /\ pc' = "Phase 3"                         (* Phase 2 ends, starts Phase 3 *)
          /\ UNCHANGED << a0, a1, a2, a3, key, g, p >>   (* The value of these variables are unchanged in this state *)
         
Phase3 == /\ pc = "Phase 3"
          /\ h0' = h0 + 1                            (* S0 receives x1, h0 increases *)
          /\ h1' = h1 + 1                            (* S1 receives x0, h1 increases *)
          /\ h2' = h2 + 1                            (* S2 receives x3, h2 increases *)
          /\ h3' = h3 + 1                            (* S3 receives x2, h3 increases *)
          /\ x0' = mod_exp(a0,x1,1,p)                (* S0 calculates x0 = x1 ^ a0 mod p as his key *)
          /\ x1' = mod_exp(a1,x0,1,p)                (* S1 calculates x2 = x0 ^ a1 mod p as his key *)
          /\ x2' = mod_exp(a2,x3,1,p)                (* S2 calculates x3 = x3 ^ a2 mod p as his key *)
          /\ x3' = mod_exp(a3,x2,1,p)                (* S3 calculates x4 = x2 ^ a3 mod p as his key *)
          /\ IF x0' = key /\ h0' = 2                 (* If the value of x0 equals key and S0 has received two *)
                 THEN /\ ck0' = TRUE                 (* messages, then ck0 becomes TRUE *)
                 ELSE /\ ck0' = ck0
                      
          /\ IF x1' = key /\ h1' = 3                 (* If the value of x1 equals key and S1 has received three *)
                 THEN /\ ck1' = TRUE                 (* messages, then ck1 becomes TRUE *)
                 ELSE /\ ck1' = ck1
                      
          /\ IF x2' = key /\ h2' = 2                 (* If the value of x2 equals key and S2 has received two *)
                 THEN /\ ck2' = TRUE                 (* messages, then ck2 becomes TRUE *)
                 ELSE /\ ck2' = ck2
                      
          /\ IF x3' = key /\ h3' = 3                 (* If the value of x3 equals key and S3 has received three *)
                 THEN /\ ck3' = TRUE                 (* messages, then ck3 becomes TRUE *)
                 ELSE /\ ck3' = ck3
                      
          /\ pc' = "Done"                            (* Phase 3 ends, the key exchange is done *)
          /\ UNCHANGED << a0, a1, a2, a3, key, g, p >>   (* The value of these variables are unchanged in this state *)
 

Next == Phase1 \/ Phase2 \/ Phase3
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

(* Checking termination *)
Termination == <>(pc = "Done")     

(* Checking wether all participants eventually receive the key at the same time *)
SameTime == (<>(ck0 /\ ck1 /\ ck2 /\ ck3)) /\ (~<>(ck0 /\ (~ck1 \/ ~ck2 \/ ~ck3))) 
/\ (~<>(ck1 /\ (~ck0 \/ ~ck2 \/ ~ck3))) /\ (~<>(ck2 /\ (~ck0 \/ ~ck1 \/ ~ck3))) 
/\ (~<>(ck3 /\ (~ck0 \/ ~ck1 \/ ~ck2)))

(* Checking wether all participants eventually receive the key *)
GetMutualKey == (<>ck0) /\ (<>ck1) /\ (<>ck2) /\ (<>ck3)          

=============================================================================
\* Modification History
\* Last modified Wed May 30 15:35:36 ICT 2018 by Emp. Elesar II
\* Created Wed May 23 13:24:05 ICT 2018 by Emp. Elesar II
