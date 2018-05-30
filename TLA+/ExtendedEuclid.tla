--------------------------- MODULE ExtendedEuclid ---------------------------

EXTENDS Integers, TLC

(* Function ExEuc(a,b) returns (d,x,y) where d = gcd(a,b) = ax + by *)

RECURSIVE ExEuc(_,_)
ExEuc(a,b) == IF (b = 0) THEN << a, 1, 0 >>                     (* if b == 0 then return (a, 1, 0) *)
              ELSE LET x == ExEuc(b, a % b) IN                  (* else x = EXTENDED-EUCLID(b, a mod b) *)
                << x[1], x[3], (x[2] - (a \div b) * x[3]) >>    (* return (x[0], x[2], x[1] - floor(a/b)*x[2] *)
                    
InverseCheck(a,b) == LET x == ExEuc(a,b) IN
                IF (x[1] = 1) THEN TRUE ELSE FALSE
                
Inverse(a,b) == LET x == ExEuc(a,b) IN
                IF (x[2] < 0) THEN x[2] + b ELSE x[2]
                     

=============================================================================
\* Modification History
\* Last modified Wed May 30 15:26:14 ICT 2018 by Emp. Elesar II
\* Created Fri May 25 16:22:34 ICT 2018 by Emp. Elesar II
