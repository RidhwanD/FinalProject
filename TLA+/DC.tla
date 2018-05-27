------------------------------- MODULE DC_mx -------------------------------

EXTENDS Integers, TLC, ModExp

VARIABLES a0, a1, a2, a3, g, key, x0, x1, x2, x3, h0, h1, h2, h3, ck0, ck1, ck2, ck3, pc, p

vars == << a0, a1, a2, a3, g, key, x0, x1, x2, x3, h0, h1, h2, h3, ck0, ck1, ck2, ck3, pc, p >>

Init == (* Global variables *)
        /\ a0 \in Nat       (* Secret exponent of P0 *)
        /\ a1 \in Nat       (* Secret exponent of P1 *)
        /\ a2 \in Nat       (* Secret exponent of P2 *)
        /\ a3 \in Nat       (* Secret exponent of P3 *)
        /\ p = 13           (* Finite field size *)
        /\ g = 2            (* Generator of Fp *)
        /\ key = mod_exp(a3,mod_exp(a2,mod_exp(a1,mod_exp(a0,g,1,p),1,p),1,p),1,p) (* Shared key *)
        /\ x0 = 0           (* Value computed by P0 *)
        /\ x1 = 0           (* Value computed by P1 *)
        /\ x2 = 0           (* Value computed by P2 *)
        /\ x3 = 0           (* Value computed by P3 *)
        /\ h0 = 0           (* Number of message received by P0 *)
        /\ h1 = 0           (* Number of message received by P1 *)
        /\ h2 = 0           (* Number of message received by P2 *)
        /\ h3 = 0           (* Number of message received by P3 *)
        /\ ck0 = FALSE      (* Boolean to indicate that P0 has received the common key *)
        /\ ck1 = FALSE      (* Boolean to indicate that P1 has received the common key *)
        /\ ck2 = FALSE      (* Boolean to indicate that P2 has received the common key *)
        /\ ck3 = FALSE      (* Boolean to indicate that P3 has received the common key *)
        /\ pc = "Phase 1"
        
Phase1 == /\ pc = "Phase 1"
          /\ x0' = mod_exp(a0,g,1,p)                  (* P0 calculates x0 = g ^ a0 mod p, sends it to P1 *)    
          /\ x2' = mod_exp(a2,g,1,p)                  (* P2 calculates x2 = g ^ a2 mod p, sends it to p3 *)
          /\ h1' = h1 + 1                            (* P1 receives x0, h1 increases *)
          /\ x1' = mod_exp(a1,x0',1,p)                (* P1 calculates x1 = x0 ^ a1 mod p, sends it to P2 and P3 *)
          /\ h3' = h3 + 1                            (* P3 receives x2, h3 increases *)
          /\ x3' = mod_exp(a3,x2',1,p)                (* P3 calculates x3 = x2 ^ a3 mod p, sends it to P0 and P1 *)
          /\ IF x0' = key /\ h0 = 2                  (* If the value of x0 equals key and P0 has received two *)
                 THEN /\ ck0' = TRUE                 (* messages, then ck0 becomes TRUE *)
                 ELSE /\ ck0' = ck0
                      
          /\ IF x1' = key /\ h1' = 3                 (* If the value of x1 equals key and P1 has received three *)
                 THEN /\ ck1' = TRUE                 (* messages, then ck1 becomes TRUE *)
                 ELSE /\ ck1' = ck1
                      
          /\ IF x2' = key /\ h2 = 2                 (* If the value of x2 equals key and P2 has received two *)
                 THEN /\ ck2' = TRUE                 (* messages, then ck2 becomes TRUE *)
                 ELSE /\ ck2' = ck2
                      
          /\ IF x3' = key /\ h3' = 3                 (* If the value of x3 equals key and P3 has received three *)
                 THEN /\ ck3' = TRUE                 (* messages, then ck3 becomes TRUE *)
                 ELSE /\ ck3' = ck3
                     
          /\ pc' = "Phase 2"                         (* Phase 1 ends, starts Phase 2 *)
          /\ UNCHANGED << a0, a1, a2, a3, key, g, p, h0, h2 >>   (* The value of these variables are unchanged *)
         
Phase2 == /\ pc = "Phase 2"
          /\ h0' = h0 + 1                            (* P0 receives x3, h0 increases *)
          /\ h1' = h1 + 1                            (* P1 receives x3, h1 increases *)
          /\ h2' = h2 + 1                            (* P2 receives x1, h2 increases *)
          /\ h3' = h3 + 1                            (* P3 receives x1, h3 increases *)
          /\ x0' = mod_exp(a0,x3,1,p)                (* P0 calculates x0 = x3 ^ a0 mod p, sends it to P1 *)
          /\ x1' = mod_exp(a1,x3,1,p)                (* P1 calculates x1 = x3 ^ a1 mod p, sends it to P0 *)
          /\ x2' = mod_exp(a2,x1,1,p)                (* P2 calculates x2 = x1 ^ a2 mod p, sends it to P3 *)
          /\ x3' = mod_exp(a3,x1,1,p)                (* P3 calculates x3 = x1 ^ a3 mod p, sends it to P2 *)
          /\ IF x0' = key /\ h0' = 2                 (* If the value of x0 equals key and P0 has received two *)
                 THEN /\ ck0' = TRUE                 (* messages, then ck0 becomes TRUE *)
                 ELSE /\ ck0' = ck0
                      
          /\ IF x1' = key /\ h1' = 3                 (* If the value of x1 equals key and P1 has received three *)
                 THEN /\ ck1' = TRUE                 (* messages, then ck1 becomes TRUE *)
                 ELSE /\ ck1' = ck1
                      
          /\ IF x2' = key /\ h2' = 2                 (* If the value of x2 equals key and P2 has received two *)
                 THEN /\ ck2' = TRUE                 (* messages, then ck2 becomes TRUE *)
                 ELSE /\ ck2' = ck2
                      
          /\ IF x3' = key /\ h3' = 3                 (* If the value of x3 equals key and P3 has received three *)
                 THEN /\ ck3' = TRUE                 (* messages, then ck3 becomes TRUE *)
                 ELSE /\ ck3' = ck3
          /\ pc' = "Phase 3"                         (* Phase 2 ends, starts Phase 3 *)
          /\ UNCHANGED << a0, a1, a2, a3, key, g, p >>   (* The value of these variables are unchanged in this state *)
         
Phase3 == /\ pc = "Phase 3"
          /\ h0' = h0 + 1                            (* P0 receives x1, h0 increases *)
          /\ h1' = h1 + 1                            (* P1 receives x0, h1 increases *)
          /\ h2' = h2 + 1                            (* P2 receives x3, h2 increases *)
          /\ h3' = h3 + 1                            (* P3 receives x2, h3 increases *)
          /\ x0' = mod_exp(a0,x1,1,p)                (* P0 calculates x0 = x1 ^ a0 mod p as his key *)
          /\ x1' = mod_exp(a1,x0,1,p)                (* P1 calculates x2 = x0 ^ a1 mod p as his key *)
          /\ x2' = mod_exp(a2,x3,1,p)                (* P2 calculates x3 = x3 ^ a2 mod p as his key *)
          /\ x3' = mod_exp(a3,x2,1,p)                (* P3 calculates x4 = x2 ^ a3 mod p as his key *)
          /\ IF x0' = key /\ h0' = 2                 (* If the value of x0 equals key and P0 has received two *)
                 THEN /\ ck0' = TRUE                 (* messages, then ck0 becomes TRUE *)
                 ELSE /\ ck0' = ck0
                      
          /\ IF x1' = key /\ h1' = 3                 (* If the value of x1 equals key and P1 has received three *)
                 THEN /\ ck1' = TRUE                 (* messages, then ck1 becomes TRUE *)
                 ELSE /\ ck1' = ck1
                      
          /\ IF x2' = key /\ h2' = 2                 (* If the value of x2 equals key and P2 has received two *)
                 THEN /\ ck2' = TRUE                 (* messages, then ck2 becomes TRUE *)
                 ELSE /\ ck2' = ck2
                      
          /\ IF x3' = key /\ h3' = 3                 (* If the value of x3 equals key and P3 has received three *)
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
\* Last modified Wed May 23 13:29:43 ICT 2018 by Emp. Elesar II
\* Created Wed May 23 13:24:05 ICT 2018 by Emp. Elesar II
