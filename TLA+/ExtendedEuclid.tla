--------------------------- MODULE ExtendedEuclid ---------------------------

EXTENDS Integers, TLC

RECURSIVE ExEuc(_,_)
ExEuc(a,b) == IF (b = 0) THEN << a, 1, 0 >>
              ELSE LET x == ExEuc(b, a % b) IN
                << x[1], x[3], (x[2] - (a \div b) * x[3]) >>
                    
CekInverse(a,b) == LET x == ExEuc(a,b) IN
                IF (x[1] = 1) THEN TRUE ELSE FALSE
                
Inverse(a,b) == LET x == ExEuc(a,b) IN
                IF (x[2] < 0) THEN x[2] + b ELSE x[2]
                     

=============================================================================
\* Modification History
\* Last modified Fri May 25 17:40:04 ICT 2018 by Emp. Elesar II
\* Created Fri May 25 16:22:34 ICT 2018 by Emp. Elesar II
