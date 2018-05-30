------------------------------ MODULE GDH1_mx ------------------------------

EXTENDS Integers, TLC, Sequences, ModExp

PrimRoot(p) == {i \in 1..(p-1): \A j \in 1..(p-1): \E k \in 1..(p-1): i ^ k % p = j}
\* GetRoot(p) == CHOOSE i \in PrimRoot(p): TRUE

VARIABLES a0, a1, a2, a3, key, g, x0, x1, x2, x3, ul, ul2, ul3, dl, dl2, dl3, ck0, ck1, 
ck2, ck3, pc, p, h0, h1, h2, h3

vars == << a0, a1, a2, a3, key, g, x0, x1, x2, x3, ul, ul2, ul3, dl, dl2, dl3, ck0, ck1, 
ck2, ck3, pc, p, h0, h1, h2, h3 >>

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
        /\ ul = <<>>        (* Upflow list generated by S0 *)
        /\ ul2 = <<>>       (* Upflow list that has been updated by S1 *)
        /\ ul3 = <<>>       (* Upflow list that has been updated by S2 *)
        /\ dl = <<>>        (* Downflow list generated by S3 *)        
        /\ dl2 = <<>>       (* Downflow list that has been updated by S2 *)
        /\ dl3 = <<>>       (* Downflow list that has been updated by S1 *)
        /\ ck0 = FALSE      (* Boolean to indicate that S0 has received the common key *)
        /\ ck1 = FALSE      (* Boolean to indicate that S1 has received the common key *)
        /\ ck2 = FALSE      (* Boolean to indicate that S2 has received the common key *)
        /\ ck3 = FALSE      (* Boolean to indicate that S3 has received the common key *)
        /\ pc = "Upflow"
        
Upflow == /\ pc = "Upflow"
          /\ x0' = mod_exp(a0,g,1,p)    (* S0 calculates x0 = g ^ a0 mod p *)
          /\ ul' = <<x0'>>              (* S0 generates upflow list ul with x0 as its member and sends it to S1 *)
          /\ h1' = h1 + 1               (* S1 receives ul from S0, h1 increases by 1 *)
          /\ x1' = mod_exp(a1,ul'[1],1,p)(* S1 computes x1 = ul[1] ^ a1 mod p *)
          /\ ul2' = Append(ul',x1')     (* S1 updates upflow list ul as ul2 by appending x1 and sends it to S2 *)
          /\ h2' = h2 + 1               (* S2 receives ul2 from S1, h2 increases by 1 *)
          /\ x2' = mod_exp(a2,ul2'[2],1,p)(* S2 computes x2 = ul2[2] ^ a2 mod p *)
          /\ ul3' = Append(ul2',x2')    (* S2 updates upflow list ul2 as ul3 by appending x2 and sends it to S3 *)
          /\ h3' = h3 + 1               (* S3 receives ul3 from S2, h3 increases by 1 *)
          /\ x3' = mod_exp(a3,ul3'[3],1,p)(* S3 computes x3 = ul3[3] ^ a3 mod p as its mutual key *)
          /\ dl' = << mod_exp(a3,g,1,p), mod_exp(a3,ul3'[1],1,p), mod_exp(a3,ul3'[2],1,p) >>  
                                        (* S3 constructs downflow list dl and sends it to S2 *)
          /\ IF x0' = key /\ h0 = 1     (* If x0 equals key and S0 has received one message from others *)
                THEN /\ ck0' = TRUE     (* then ck0 becomes TRUE *)
                ELSE /\ TRUE
                     /\ ck0' = ck0
          /\ IF x1' = key /\ h1' = 2    (* If x1 equals key and S1 has received two messages from others *)
                THEN /\ ck1' = TRUE     (* then ck1 becomes TRUE *)
                ELSE /\ TRUE
                     /\ ck1' = ck1
          /\ IF x2' = key /\ h2' = 2    (* If x2 equals key and S2 has received two messages from others *)
                THEN /\ ck2' = TRUE     (* then ck2 becomes TRUE *)
                ELSE /\ TRUE
                     /\ ck2' = ck2
          /\ IF x3' = key /\ h3' = 1    (* If x3 equals key and S3 has received one message from others *)
                THEN /\ ck3' = TRUE     (* then ck3 becomes TRUE *)
                ELSE /\ TRUE
                     /\ ck3' = ck3
          /\ pc' = "Downflow"           (* The upflow phase is done, starts the downflow phase *)
          /\ UNCHANGED << a0, a1, a2, a3, g, p, dl2, dl3, key, h0 >>   (* The value of these variables are unchanged *)
          
Downflow == /\ pc = "Downflow"
            /\ h2' = h2 + 1             (* S2 receives dl from S3, h2 increases by 1 *)
            /\ x2' = mod_exp(a2,dl[3],1,p)(* S2 computes x2 = dl[3] ^ a2 mod p as its mutual key *)
            /\ dl2' = << mod_exp(a2,dl[1],1,p), mod_exp(a2,dl[2],1,p) >>    
                                        (* S2 updates downflow list dl as dl2 and sends it to S1 *)
            /\ h1' = h1 + 1             (* S1 receives dl2 from S2, h1 increases by 1 *)
            /\ x1' = mod_exp(a1,dl2'[2],1,p)(* S1 computes x1 = dl2[2] ^ a1 mod p as its mutual key *)
            /\ dl3' = << mod_exp(a1,dl2'[1],1,p) >>    (* S1 updates downflow list dl2 as dl3 and sends it to S0 *)
            /\ h0' = h0 + 1             (* S0 receives dl3 from S1, h0 increases by 1 *)
            /\ x0' = mod_exp(a0,dl3'[1],1,p)(* S0 computes x0 = dl3[1] ^ a0 mod p as its mutual key *)
            /\ IF x0' = key /\ h0' = 1  (* If x0 equals key and S0 has received one message from others *)
                 THEN /\ ck0' = TRUE    (* then ck0 becomes TRUE *)
                 ELSE /\ TRUE
                      /\ ck0' = ck0
            /\ IF x1' = key /\ h1' = 2  (* If x1 equals key and S1 has received two messages from others *)
                 THEN /\ ck1' = TRUE    (* then ck1 becomes TRUE *)
                 ELSE /\ TRUE
                      /\ ck1' = ck1
            /\ IF x2' = key /\ h2' = 2  (* If x2 equals key and S2 has received two messages from others *)
                 THEN /\ ck2' = TRUE    (* then ck2 becomes TRUE *)
                 ELSE /\ TRUE
                      /\ ck2' = ck2
            /\ IF x3 = key /\ h3 = 1    (* If x3 equals key and S3 has received one message from others *)
                 THEN /\ ck3' = TRUE    (* then ck3 becomes TRUE *)
                 ELSE /\ TRUE
                      /\ ck3' = ck3
            /\ pc' = "Done"             (* The key exchange is done *)
            /\ UNCHANGED << a0, a1, a2, a3, g, p, ul, ul2, ul3, dl, key, x3, h3 >>   
               (* The value of these variables are unchanged in this state *)

Next == Upflow \/ Downflow
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
\* Last modified Wed May 30 15:36:08 ICT 2018 by Emp. Elesar II
\* Created Wed May 23 14:30:14 ICT 2018 by Emp. Elesar II
