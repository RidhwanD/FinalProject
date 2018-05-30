------------------------------- MODULE ING_mx -------------------------------

EXTENDS Naturals, TLC, ModExp

VARIABLES a0, a1, a2, a3, g, p, x0, x1, x2, x3, ck0, ck1, ck2, 
          ck3, i, pc, h0, h1, h2, h3, key

vars == << a0, a1, a2, a3, g, p, x0, x1, x2, x3, ck0, ck1, ck2, 
           ck3, i, pc, h0, h1, h2, h3, key >>

Init == (* Global variables *)
        /\ a0 \in Nat       (* Secret exponent of P0 *)
        /\ a1 \in Nat       (* Secret exponent of P1 *)
        /\ a2 \in Nat       (* Secret exponent of P2 *)
        /\ a3 \in Nat       (* Secret exponent of P3 *)
        /\ p = 13           (* Finite field size *)
        /\ g = 2            (* Generator of Fp *)
        /\ key = mod_exp(a3,mod_exp(a2,mod_exp(a1,mod_exp(a0,g,1,p),1,p),1,p),1,p)  (* Shared key *)
        /\ x0 = g           (* Value computed by P0 *)
        /\ x1 = g           (* Value computed by P1 *)
        /\ x2 = g           (* Value computed by P2 *)
        /\ x3 = g           (* Value computed by P3 *)
        /\ h0 = 0           (* Number of message received by P0 *)
        /\ h1 = 0           (* Number of message received by P1 *)
        /\ h2 = 0           (* Number of message received by P2 *)
        /\ h3 = 0           (* Number of message received by P3 *)
        /\ ck0 = FALSE      (* Boolean to indicate that P0 has received the common key *)
        /\ ck1 = FALSE      (* Boolean to indicate that P1 has received the common key *)
        /\ ck2 = FALSE      (* Boolean to indicate that P2 has received the common key *)
        /\ ck3 = FALSE      (* Boolean to indicate that P3 has received the common key *)
        /\ i = 1            (* Phase counter *)
        /\ pc = "Phase"
        
Phase == /\ pc = "Phase"    (* For every phase *)
         /\ IF i > 1        (* If it's not phase 1 *)
               THEN /\ h0' = h0 + 1     (* Each participants has received a message from others *)
                    /\ h1' = h1 + 1     (* Hence, each hi increases by 1 *)
                    /\ h2' = h2 + 1
                    /\ h3' = h3 + 1
               ELSE /\ TRUE
                    /\ h0' = h0
                    /\ h1' = h1
                    /\ h2' = h2
                    /\ h3' = h3
         /\ x0' = mod_exp(a0,x3,1,p)     (* P0 calculates x0 = x3 ^ a0 mod p, and sends it to P1 *)
         /\ x1' = mod_exp(a1,x0,1,p)     (* P1 calculates x1 = x0 ^ a1 mod p, and sends it to P2 *)
         /\ x2' = mod_exp(a2,x1,1,p)     (* P2 calculates x2 = x1 ^ a2 mod p, and sends it to P3 *)
         /\ x3' = mod_exp(a3,x2,1,p)     (* P3 calculates x3 = x2 ^ a3 mod p, and sends it to P0 *)
         /\ IF x0' = key /\ h0' = 3      (* If the value of x0 equals key and P10 has received three *)
               THEN /\ ck0' = TRUE       (* messages, then ck0 becomes TRUE *)
               ELSE /\ TRUE
                    /\ ck0' = ck0
         /\ IF x1' = key /\ h1' = 3      (* If the value of x1 equals key and P1 has received three *)
               THEN /\ ck1' = TRUE       (* messages, then ck1 becomes TRUE *)
               ELSE /\ TRUE
                    /\ ck1' = ck1
         /\ IF x2' = key /\ h2' = 3      (* If the value of x2 equals key and P2 has received three *)
               THEN /\ ck2' = TRUE       (* messages, then ck2 becomes TRUE *)
               ELSE /\ TRUE
                    /\ ck2' = ck2
         /\ IF x3' = key /\ h3' = 3      (* If the value of x3 equals key and P3 has received three *)
               THEN /\ ck3' = TRUE       (* messages, then ck3 becomes TRUE *)
               ELSE /\ TRUE
                    /\ ck3' = ck3
         /\ i' = i + 1                   (* Go to next phase, i increases by 1 *)
         /\ IF i' = 5
               THEN /\ pc' = "Done"      (* If i is 5, then the key exchange is done *)
               ELSE /\ pc' = "Phase"
         /\ UNCHANGED << a0, a1, a2, a3, g, key, p >>    (* The value of these variables are unchanged in this state *)

Next == Phase
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
\* Last modified Wed May 23 16:22:36 ICT 2018 by Emp. Elesar II
\* Created Wed May 23 16:20:49 ICT 2018 by Emp. Elesar II
