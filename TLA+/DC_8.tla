-------------------------------- MODULE DC8 --------------------------------

EXTENDS Integers, TLC, ModExp

VARIABLES a0, a1, a2, a3, a4, a5, a6, a7, g, key, x0, x1, x2, x3, x4, x5, x6, x7, 
h0, h1, h2, h3, h4, h5, h6, h7, ck0, ck1, ck2, ck3, ck4, ck5, ck6, ck7, pc, p

vars == << a0, a1, a2, a3, a4, a5, a6, a7, g, key, x0, x1, x2, x3, x4, x5, x6, x7, 
h0, h1, h2, h3, h4, h5, h6, h7, ck0, ck1, ck2, ck3, ck4, ck5, ck6, ck7, pc, p >>

Init == (* Global variables *)
        /\ a0 \in Nat       (* Secret exponent of S0 *)
        /\ a1 \in Nat       (* Secret exponent of S1 *)
        /\ a2 \in Nat       (* Secret exponent of S2 *)
        /\ a3 \in Nat       (* Secret exponent of S3 *)
        /\ a4 \in Nat       (* Secret exponent of S4 *)
        /\ a5 \in Nat       (* Secret exponent of S5 *)
        /\ a6 \in Nat       (* Secret exponent of S6 *)
        /\ a7 \in Nat       (* Secret exponent of S7 *)
        /\ p = 13           (* Finite field size *)
        /\ g = 2            (* Generator of Fp *)
        /\ key = mod_exp(a7,mod_exp(a6,mod_exp(a5,mod_exp(a4,mod_exp(a3,mod_exp(a2,mod_exp(a1,mod_exp(a0,g,1,p),1,p),1,p),1,p),1,p),1,p),1,p),1,p) 
                            (* Shared key *)
        /\ x0 = 0           (* Value computed by S0 *)
        /\ x1 = 0           (* Value computed by S1 *)
        /\ x2 = 0           (* Value computed by S2 *)
        /\ x3 = 0           (* Value computed by S3 *)
        /\ x4 = 0           (* Value computed by S4 *)
        /\ x5 = 0           (* Value computed by S5 *)
        /\ x6 = 0           (* Value computed by S6 *)
        /\ x7 = 0           (* Value computed by S7 *)
        /\ h0 = 0           (* Number of message received by S0 *)
        /\ h1 = 0           (* Number of message received by S1 *)
        /\ h2 = 0           (* Number of message received by S2 *)
        /\ h3 = 0           (* Number of message received by S3 *)
        /\ h4 = 0           (* Number of message received by S4 *)
        /\ h5 = 0           (* Number of message received by S5 *)
        /\ h6 = 0           (* Number of message received by S6 *)
        /\ h7 = 0           (* Number of message received by S7 *)
        /\ ck0 = FALSE      (* Boolean to indicate that S0 has received the common key *)
        /\ ck1 = FALSE      (* Boolean to indicate that S1 has received the common key *)
        /\ ck2 = FALSE      (* Boolean to indicate that S2 has received the common key *)
        /\ ck3 = FALSE      (* Boolean to indicate that S3 has received the common key *)
        /\ ck4 = FALSE      (* Boolean to indicate that S4 has received the common key *)
        /\ ck5 = FALSE      (* Boolean to indicate that S5 has received the common key *)
        /\ ck6 = FALSE      (* Boolean to indicate that S6 has received the common key *)
        /\ ck7 = FALSE      (* Boolean to indicate that S7 has received the common key *)
        /\ pc = "Phase 1"
        
Phase1 == /\ pc = "Phase 1"
          /\ x0' = mod_exp(a0,g,1,p)                 (* S0 calculates x0 = g ^ a0 mod p, sends it to S1 *)    
          /\ h1' = h1 + 1                            (* S1 receives x0, h1 increases *)
          /\ x1' = mod_exp(a1,x0',1,p)               (* S1 calculates x1 = x0 ^ a1 mod p, sends it to S2 *)
          /\ h2' = h2 + 1                            (* S2 receives x1, h2 increases *)
          /\ x2' = mod_exp(a2,x1',1,p)               (* S2 calculates x2 = x1 ^ a2 mod p, sends it to S3 *)
          /\ h3' = h3 + 1                            (* S3 receives x2, h3 increases *)
          /\ x3' = mod_exp(a3,x2',1,p)               (* S3 calculates x3 = x2 ^ a3 mod p, sends it to S4 and S6 *)
          /\ x4' = mod_exp(a4,g,1,p)                 (* S4 calculates x4 = g ^ a4 mod p, sends it to S3 *)
          /\ h5' = h5 + 1                            (* S5 receives x4, h5 increases *)
          /\ x5' = mod_exp(a5,x4',1,p)               (* S5 calculates x5 = x4 ^ a5 mod p, sends it to S6 *)
          /\ h6' = h6 + 1                            (* S6 receives x5, h6 increases *)
          /\ x6' = mod_exp(a6,x5',1,p)               (* S6 calculates x6 = x5 ^ a6 mod p, sends it to S7 *)
          /\ h7' = h7 + 1                            (* S7 receives x6, h7 increases *)
          /\ x7' = mod_exp(a7,x6',1,p)               (* S7 calculates x7 = x6 ^ a7 mod p, sends it to S0 and S2 *)
          
          /\ IF x0' = key /\ h0 = 3                  (* If the value of x0 equals key and S0 has received three *)
                 THEN /\ ck0' = TRUE                 (* messages, then ck0 becomes TRUE *)
                 ELSE /\ ck0' = ck0
                      
          /\ IF x1' = key /\ h1' = 4                 (* If the value of x1 equals key and S1 has received four *)
                 THEN /\ ck1' = TRUE                 (* messages, then ck1 becomes TRUE *)
                 ELSE /\ ck1' = ck1
                      
          /\ IF x2' = key /\ h2' = 4                 (* If the value of x2 equals key and S2 has received four *)
                 THEN /\ ck2' = TRUE                 (* messages, then ck2 becomes TRUE *)
                 ELSE /\ ck2' = ck2
                      
          /\ IF x3' = key /\ h3' = 4                 (* If the value of x3 equals key and S3 has received four *)
                 THEN /\ ck3' = TRUE                 (* messages, then ck3 becomes TRUE *)
                 ELSE /\ ck3' = ck3
                     
          /\ IF x4' = key /\ h4 = 3                  (* If the value of x4 equals key and S4 has received three *)
                 THEN /\ ck4' = TRUE                 (* messages, then ck0 becomes TRUE *)
                 ELSE /\ ck4' = ck4
                      
          /\ IF x5' = key /\ h5' = 4                 (* If the value of x5 equals key and S5 has received four *)
                 THEN /\ ck5' = TRUE                 (* messages, then ck1 becomes TRUE *)
                 ELSE /\ ck5' = ck5
                      
          /\ IF x6' = key /\ h6' = 4                 (* If the value of x6 equals key and S6 has received four *)
                 THEN /\ ck6' = TRUE                 (* messages, then ck2 becomes TRUE *)
                 ELSE /\ ck6' = ck6
                      
          /\ IF x7' = key /\ h7' = 4                 (* If the value of x7 equals key and S7 has received four *)
                 THEN /\ ck7' = TRUE                 (* messages, then ck3 becomes TRUE *)
                 ELSE /\ ck7' = ck7
                     
          /\ pc' = "Phase 2"                         (* Phase 1 ends, starts Phase 2 *)
          /\ UNCHANGED << a0, a1, a2, a3, a4, a5, a6, a7, key, g, p, h0, h4 >>   
                                                     (* The value of these variables are unchanged *)
          
Phase2 == /\ pc = "Phase 2"
          /\ h0' = h0 + 1                            (* S0 receives x7 from phase 1, h0 increases *)
          /\ x0' = mod_exp(a0,x7,1,p)                (* S0 calculates x0 = x7 ^ a0 mod p, sends it to S1 *) 
          /\ h2' = h2 + 1                            (* S2 receives x7 from phase 1, h2 increases *)   
          /\ x2' = mod_exp(a2,x7,1,p)                (* S2 calculates x2 = x7 ^ a2 mod p, sends it to S3 *)
          /\ h1' = h1 + 1                            (* S1 receives x0, h1 increases *)
          /\ x1' = mod_exp(a1,x0',1,p)               (* S1 calculates x1 = x0 ^ a1 mod p, sends it to S2 and S3 *)
          /\ h3' = h3 + 1                            (* S3 receives x2, h3 increases *)
          /\ x3' = mod_exp(a3,x2',1,p)               (* S3 calculates x3 = x2 ^ a3 mod p, sends it to S0 and S1 *)
          /\ h4' = h4 + 1                            (* S4 receives x3 from phase 1, h4 increases *)
          /\ x4' = mod_exp(a4,x3,1,p)                (* S4 calculates x4 = x3 ^ a4 mod p, sends it to S5 *) 
          /\ h6' = h6 + 1                            (* S6 receives x3 from phase 1, h6 increases *)   
          /\ x6' = mod_exp(a6,x3,1,p)                (* S6 calculates x6 = x3 ^ a6 mod p, sends it to S7 *)
          /\ h5' = h5 + 1                            (* S5 receives x4, h5 increases *)
          /\ x5' = mod_exp(a5,x4',1,p)               (* S5 calculates x5 = x4 ^ a5 mod p, sends it to S6 and S7 *)
          /\ h7' = h7 + 1                            (* S7 receives x6, h7 increases *)
          /\ x7' = mod_exp(a7,x6',1,p)               (* S7 calculates x7 = x6 ^ a7 mod p, sends it to S4 and S5 *)
          
          /\ IF x0' = key /\ h0' = 3                 (* If the value of x0 equals key and S0 has received three *)
                 THEN /\ ck0' = TRUE                 (* messages, then ck0 becomes TRUE *)
                 ELSE /\ ck0' = ck0
                      
          /\ IF x1' = key /\ h1' = 4                 (* If the value of x1 equals key and S1 has received four *)
                 THEN /\ ck1' = TRUE                 (* messages, then ck1 becomes TRUE *)
                 ELSE /\ ck1' = ck1
                      
          /\ IF x2' = key /\ h2' = 4                 (* If the value of x2 equals key and S2 has received four *)
                 THEN /\ ck2' = TRUE                 (* messages, then ck2 becomes TRUE *)
                 ELSE /\ ck2' = ck2
                      
          /\ IF x3' = key /\ h3' = 4                 (* If the value of x3 equals key and S3 has received four *)
                 THEN /\ ck3' = TRUE                 (* messages, then ck3 becomes TRUE *)
                 ELSE /\ ck3' = ck3
                     
          /\ IF x4' = key /\ h4' = 3                 (* If the value of x4 equals key and S4 has received three *)
                 THEN /\ ck4' = TRUE                 (* messages, then ck0 becomes TRUE *)
                 ELSE /\ ck4' = ck4
                      
          /\ IF x5' = key /\ h5' = 4                 (* If the value of x5 equals key and S5 has received four *)
                 THEN /\ ck5' = TRUE                 (* messages, then ck1 becomes TRUE *)
                 ELSE /\ ck5' = ck5
                      
          /\ IF x6' = key /\ h6' = 4                 (* If the value of x6 equals key and S6 has received four *)
                 THEN /\ ck6' = TRUE                 (* messages, then ck2 becomes TRUE *)
                 ELSE /\ ck6' = ck6
                      
          /\ IF x7' = key /\ h7' = 4                 (* If the value of x7 equals key and S7 has received four *)
                 THEN /\ ck7' = TRUE                 (* messages, then ck3 becomes TRUE *)
                 ELSE /\ ck7' = ck7
                     
          /\ pc' = "Phase 3"                         (* Phase 1 ends, starts Phase 2 *)
          /\ UNCHANGED << a0, a1, a2, a3, a4, a5, a6, a7, key, g, p >>   (* The value of these variables are unchanged *)
         
Phase3 == /\ pc = "Phase 3"
          /\ h0' = h0 + 1                            (* S0 receives x3, h0 increases *)
          /\ h1' = h1 + 1                            (* S1 receives x3, h1 increases *)
          /\ h2' = h2 + 1                            (* S2 receives x1, h2 increases *)
          /\ h3' = h3 + 1                            (* S3 receives x1, h3 increases *)
          /\ x0' = mod_exp(a0,x3,1,p)                (* S0 calculates x0 = x3 ^ a0 mod p, sends it to S1 *)
          /\ x1' = mod_exp(a1,x3,1,p)                (* S1 calculates x1 = x3 ^ a1 mod p, sends it to S0 *)
          /\ x2' = mod_exp(a2,x1,1,p)                (* S2 calculates x2 = x1 ^ a2 mod p, sends it to S3 *)
          /\ x3' = mod_exp(a3,x1,1,p)                (* S3 calculates x3 = x1 ^ a3 mod p, sends it to S2 *)
          /\ h4' = h4 + 1                            (* S4 receives x7, h4 increases *)
          /\ h5' = h5 + 1                            (* S5 receives x7, h5 increases *)
          /\ h6' = h6 + 1                            (* S6 receives x5, h6 increases *)
          /\ h7' = h7 + 1                            (* S7 receives x5, h7 increases *)
          /\ x4' = mod_exp(a4,x7,1,p)                (* S4 calculates x4 = x7 ^ a4 mod p, sends it to S5 *)
          /\ x5' = mod_exp(a5,x7,1,p)                (* S5 calculates x5 = x7 ^ a5 mod p, sends it to S4 *)
          /\ x6' = mod_exp(a6,x5,1,p)                (* S6 calculates x6 = x5 ^ a6 mod p, sends it to S7 *)
          /\ x7' = mod_exp(a7,x5,1,p)                (* S7 calculates x7 = x5 ^ a7 mod p, sends it to S6 *)
          
          /\ IF x0' = key /\ h0' = 3                 (* If the value of x0 equals key and S0 has received three *)
                 THEN /\ ck0' = TRUE                 (* messages, then ck0 becomes TRUE *)
                 ELSE /\ ck0' = ck0
                      
          /\ IF x1' = key /\ h1' = 4                 (* If the value of x1 equals key and S1 has received four *)
                 THEN /\ ck1' = TRUE                 (* messages, then ck1 becomes TRUE *)
                 ELSE /\ ck1' = ck1
                      
          /\ IF x2' = key /\ h2' = 4                 (* If the value of x2 equals key and S2 has received four *)
                 THEN /\ ck2' = TRUE                 (* messages, then ck2 becomes TRUE *)
                 ELSE /\ ck2' = ck2
                      
          /\ IF x3' = key /\ h3' = 4                 (* If the value of x3 equals key and S3 has received four *)
                 THEN /\ ck3' = TRUE                 (* messages, then ck3 becomes TRUE *)
                 ELSE /\ ck3' = ck3
                     
          /\ IF x4' = key /\ h4' = 3                 (* If the value of x4 equals key and S4 has received three *)
                 THEN /\ ck4' = TRUE                 (* messages, then ck0 becomes TRUE *)
                 ELSE /\ ck4' = ck4
                      
          /\ IF x5' = key /\ h5' = 4                 (* If the value of x5 equals key and S5 has received four *)
                 THEN /\ ck5' = TRUE                 (* messages, then ck1 becomes TRUE *)
                 ELSE /\ ck5' = ck5
                      
          /\ IF x6' = key /\ h6' = 4                 (* If the value of x6 equals key and S6 has received four *)
                 THEN /\ ck6' = TRUE                 (* messages, then ck2 becomes TRUE *)
                 ELSE /\ ck6' = ck6
                      
          /\ IF x7' = key /\ h7' = 4                 (* If the value of x7 equals key and S7 has received four *)
                 THEN /\ ck7' = TRUE                 (* messages, then ck3 becomes TRUE *)
                 ELSE /\ ck7' = ck7
                 
          /\ pc' = "Phase 4"                         (* Phase 2 ends, starts Phase 3 *)
          /\ UNCHANGED << a0, a1, a2, a3, a4, a5, a6, a7, key, g, p >>   (* The value of these variables are unchanged *)
         
Phase4 == /\ pc = "Phase 4"
          /\ h0' = h0 + 1                            (* S0 receives x1, h0 increases *)
          /\ h1' = h1 + 1                            (* S1 receives x0, h1 increases *)
          /\ h2' = h2 + 1                            (* S2 receives x3, h2 increases *)
          /\ h3' = h3 + 1                            (* S3 receives x2, h3 increases *)
          /\ x0' = mod_exp(a0,x1,1,p)                (* S0 calculates x0 = x1 ^ a0 mod p as his key *)
          /\ x1' = mod_exp(a1,x0,1,p)                (* S1 calculates x2 = x0 ^ a1 mod p as his key *)
          /\ x2' = mod_exp(a2,x3,1,p)                (* S2 calculates x3 = x3 ^ a2 mod p as his key *)
          /\ x3' = mod_exp(a3,x2,1,p)                (* S3 calculates x4 = x2 ^ a3 mod p as his key *)
          /\ h4' = h4 + 1                            (* S4 receives x5, h4 increases *)
          /\ h5' = h5 + 1                            (* S5 receives x4, h5 increases *)
          /\ h6' = h6 + 1                            (* S6 receives x7, h6 increases *)
          /\ h7' = h7 + 1                            (* S7 receives x6, h7 increases *)
          /\ x4' = mod_exp(a4,x5,1,p)                (* S4 calculates x4 = x5 ^ a4 mod p as his key *)
          /\ x5' = mod_exp(a5,x4,1,p)                (* S5 calculates x5 = x4 ^ a5 mod p as his key *)
          /\ x6' = mod_exp(a6,x7,1,p)                (* S6 calculates x6 = x7 ^ a6 mod p as his key *)
          /\ x7' = mod_exp(a7,x6,1,p)                (* S7 calculates x7 = x6 ^ a7 mod p as his key *)
          
          /\ IF x0' = key /\ h0' = 3                 (* If the value of x0 equals key and S0 has received three *)
                 THEN /\ ck0' = TRUE                 (* messages, then ck0 becomes TRUE *)
                 ELSE /\ ck0' = ck0
                      
          /\ IF x1' = key /\ h1' = 4                 (* If the value of x1 equals key and S1 has received four *)
                 THEN /\ ck1' = TRUE                 (* messages, then ck1 becomes TRUE *)
                 ELSE /\ ck1' = ck1
                      
          /\ IF x2' = key /\ h2' = 4                 (* If the value of x2 equals key and S2 has received four *)
                 THEN /\ ck2' = TRUE                 (* messages, then ck2 becomes TRUE *)
                 ELSE /\ ck2' = ck2
                      
          /\ IF x3' = key /\ h3' = 4                 (* If the value of x3 equals key and S3 has received four *)
                 THEN /\ ck3' = TRUE                 (* messages, then ck3 becomes TRUE *)
                 ELSE /\ ck3' = ck3
                     
          /\ IF x4' = key /\ h4' = 3                 (* If the value of x4 equals key and S4 has received three *)
                 THEN /\ ck4' = TRUE                 (* messages, then ck0 becomes TRUE *)
                 ELSE /\ ck4' = ck4
                      
          /\ IF x5' = key /\ h5' = 4                 (* If the value of x5 equals key and S5 has received four *)
                 THEN /\ ck5' = TRUE                 (* messages, then ck1 becomes TRUE *)
                 ELSE /\ ck5' = ck5
                      
          /\ IF x6' = key /\ h6' = 4                 (* If the value of x6 equals key and S6 has received four *)
                 THEN /\ ck6' = TRUE                 (* messages, then ck2 becomes TRUE *)
                 ELSE /\ ck6' = ck6
                      
          /\ IF x7' = key /\ h7' = 4                 (* If the value of x7 equals key and S7 has received four *)
                 THEN /\ ck7' = TRUE                 (* messages, then ck3 becomes TRUE *)
                 ELSE /\ ck7' = ck7
                      
          /\ pc' = "Done"                            (* Phase 3 ends, the key exchange is done *)
          /\ UNCHANGED << a0, a1, a2, a3, a4, a5, a6, a7, key, g, p >>   (* The value of these variables are unchanged *)
         
Next == Phase1 \/ Phase2 \/ Phase3 \/ Phase4
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

(* Checking termination *)
Termination == <>(pc = "Done")     

(* Checking wether all participants eventually receive the key at the same time *)
SameTime == (<>(ck0 /\ ck1 /\ ck2 /\ ck3 /\ ck4 /\ ck5 /\ ck6 /\ ck7)) 
/\ (~<>(ck0 /\ (~ck1 \/ ~ck2 \/ ~ck3 \/ ~ck4 \/ ~ck5 \/ ~ck6 \/ ~ck7))) 
/\ (~<>(ck1 /\ (~ck0 \/ ~ck2 \/ ~ck3 \/ ~ck4 \/ ~ck5 \/ ~ck6 \/ ~ck7))) 
/\ (~<>(ck2 /\ (~ck0 \/ ~ck1 \/ ~ck3 \/ ~ck4 \/ ~ck5 \/ ~ck6 \/ ~ck7))) 
/\ (~<>(ck3 /\ (~ck0 \/ ~ck1 \/ ~ck2 \/ ~ck4 \/ ~ck5 \/ ~ck6 \/ ~ck7)))
/\ (~<>(ck4 /\ (~ck0 \/ ~ck1 \/ ~ck2 \/ ~ck3 \/ ~ck5 \/ ~ck6 \/ ~ck7)))
/\ (~<>(ck5 /\ (~ck0 \/ ~ck1 \/ ~ck2 \/ ~ck3 \/ ~ck4 \/ ~ck6 \/ ~ck7)))
/\ (~<>(ck6 /\ (~ck0 \/ ~ck1 \/ ~ck2 \/ ~ck3 \/ ~ck4 \/ ~ck5 \/ ~ck7)))
/\ (~<>(ck7 /\ (~ck0 \/ ~ck1 \/ ~ck2 \/ ~ck3 \/ ~ck4 \/ ~ck5 \/ ~ck6)))

(* Checking wether all participants eventually receive the key *)
GetMutualKey == (<>ck0) /\ (<>ck1) /\ (<>ck2) /\ (<>ck3) /\ (<>ck4) /\ (<>ck5) /\ (<>ck6) /\ (<>ck7)          

=============================================================================
\* Modification History
\* Last modified Wed May 30 16:43:10 ICT 2018 by Emp. Elesar II
\* Created Wed May 30 15:26:59 ICT 2018 by Emp. Elesar II
