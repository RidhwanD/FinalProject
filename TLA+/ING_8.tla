------------------------------- MODULE ING_8 -------------------------------

EXTENDS Naturals, TLC, ModExp

VARIABLES a0, a1, a2, a3, a4, a5, a6, a7, g, key, x0, x1, x2, x3, x4, x5, x6, x7, 
h0, h1, h2, h3, h4, h5, h6, h7, ck0, ck1, ck2, ck3, ck4, ck5, ck6, ck7, pc, p, i

vars == << a0, a1, a2, a3, a4, a5, a6, a7, g, key, x0, x1, x2, x3, x4, x5, x6, x7, 
h0, h1, h2, h3, h4, h5, h6, h7, ck0, ck1, ck2, ck3, ck4, ck5, ck6, ck7, pc, p, i >>

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
        /\ x0 = g           (* Value computed by S0 *)
        /\ x1 = g           (* Value computed by S1 *)
        /\ x2 = g           (* Value computed by S2 *)
        /\ x3 = g           (* Value computed by S3 *)
        /\ x4 = g           (* Value computed by S4 *)
        /\ x5 = g           (* Value computed by S5 *)
        /\ x6 = g           (* Value computed by S6 *)
        /\ x7 = g           (* Value computed by S7 *)
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
        /\ i = 1            (* Phase counter *)
        /\ pc = "Phase"
        
Phase == /\ pc = "Phase"    (* For every phase *)
         /\ IF i > 1        (* If it's not phase 1 *)
               THEN /\ h0' = h0 + 1     (* Each participants has received a message from others *)
                    /\ h1' = h1 + 1     (* Hence, each hi increases by 1 *)
                    /\ h2' = h2 + 1
                    /\ h3' = h3 + 1
                    /\ h4' = h4 + 1
                    /\ h5' = h5 + 1
                    /\ h6' = h6 + 1
                    /\ h7' = h7 + 1
               ELSE /\ h0' = h0
                    /\ h1' = h1
                    /\ h2' = h2
                    /\ h3' = h3
                    /\ h4' = h4
                    /\ h5' = h5
                    /\ h6' = h6
                    /\ h7' = h7
         /\ x0' = mod_exp(a0,x7,1,p)     (* S0 calculates x0 = x7 ^ a0 mod p, and sends it to S1 *)
         /\ x1' = mod_exp(a1,x0,1,p)     (* S1 calculates x1 = x0 ^ a1 mod p, and sends it to S2 *)
         /\ x2' = mod_exp(a2,x1,1,p)     (* S2 calculates x2 = x1 ^ a2 mod p, and sends it to S3 *)
         /\ x3' = mod_exp(a3,x2,1,p)     (* S3 calculates x3 = x2 ^ a3 mod p, and sends it to S4 *)
         /\ x4' = mod_exp(a4,x3,1,p)     (* S4 calculates x4 = x3 ^ a4 mod p, and sends it to S5 *)
         /\ x5' = mod_exp(a5,x4,1,p)     (* S5 calculates x5 = x4 ^ a5 mod p, and sends it to S6 *)
         /\ x6' = mod_exp(a6,x5,1,p)     (* S6 calculates x6 = x5 ^ a6 mod p, and sends it to S7 *)
         /\ x7' = mod_exp(a7,x6,1,p)     (* S7 calculates x7 = x6 ^ a7 mod p, and sends it to S0 *)
         
         /\ IF x0' = key /\ h0' = 7                 (* If the value of x0 equals key and S0 has received seven *)
                THEN /\ ck0' = TRUE                 (* messages, then ck0 becomes TRUE *)
                ELSE /\ ck0' = ck0
                      
         /\ IF x1' = key /\ h1' = 7                 (* If the value of x1 equals key and S1 has received seven *)
                THEN /\ ck1' = TRUE                 (* messages, then ck1 becomes TRUE *)
                ELSE /\ ck1' = ck1
                     
         /\ IF x2' = key /\ h2' = 7                 (* If the value of x2 equals key and S2 has received seven *)
                THEN /\ ck2' = TRUE                 (* messages, then ck2 becomes TRUE *)
                ELSE /\ ck2' = ck2
                     
         /\ IF x3' = key /\ h3' = 7                 (* If the value of x3 equals key and S3 has received seven *)
                THEN /\ ck3' = TRUE                 (* messages, then ck3 becomes TRUE *)
                ELSE /\ ck3' = ck3
                    
         /\ IF x4' = key /\ h4' = 7                 (* If the value of x4 equals key and S4 has received seven *)
                THEN /\ ck4' = TRUE                 (* messages, then ck0 becomes TRUE *)
                ELSE /\ ck4' = ck4
                     
         /\ IF x5' = key /\ h5' = 7                 (* If the value of x5 equals key and S5 has received seven *)
                THEN /\ ck5' = TRUE                 (* messages, then ck1 becomes TRUE *)
                ELSE /\ ck5' = ck5
                     
         /\ IF x6' = key /\ h6' = 7                 (* If the value of x6 equals key and S6 has received seven *)
                THEN /\ ck6' = TRUE                 (* messages, then ck2 becomes TRUE *)
                ELSE /\ ck6' = ck6
                     
         /\ IF x7' = key /\ h7' = 7                 (* If the value of x7 equals key and S7 has received seven *)
                THEN /\ ck7' = TRUE                 (* messages, then ck3 becomes TRUE *)
                ELSE /\ ck7' = ck7
         
         /\ i' = i + 1                   (* Go to next phase, i increases by 1 *)
         /\ IF i' = 9
               THEN /\ pc' = "Done"      (* If i is 9, then the key exchange is done *)
               ELSE /\ pc' = "Phase"
         /\ UNCHANGED << a0, a1, a2, a3, a4, a5, a6, a7, g, key, p >>    
                                         (* The value of these variables are unchanged in this state *)

Next == Phase
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
\* Last modified Wed May 30 17:08:46 ICT 2018 by Emp. Elesar II
\* Created Wed May 30 16:44:57 ICT 2018 by Emp. Elesar II
