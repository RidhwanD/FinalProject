------------------------------- MODULE ModExp -------------------------------
EXTENDS Integers, TLC

(* Function mod_exp(e,g,b,N) returns the value of g^e mod N *)

RECURSIVE mod_exp(_,_,_,_)
mod_exp(A,a,b,N) == 
            IF (A = 0) THEN b
            ELSE LET y == 
                 IF (A % 2 = 0) THEN b ELSE (b * a) % N 
                 IN mod_exp(A \div 2, a ^ 2 % N, y, N)
                                    
=============================================================================
\* Modification History
\* Last modified Sun May 27 13:30:16 ICT 2018 by Emp. Elesar II
\* Created Wed May 23 12:18:29 ICT 2018 by Emp. Elesar II
