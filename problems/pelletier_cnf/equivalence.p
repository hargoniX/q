



cnf(i_0_6, negated_conjecture, (equ(esk3_0,esk2_0))).
cnf(i_0_7, negated_conjecture, (equ(esk4_0,esk3_0))).

cnf(i_0_5, negated_conjecture, (~equ(esk4_0,esk2_0))).

cnf(i_0_3, plain, (contains(X3,X2)|~equ(X3,X1)|~contains(X1,X2))).
cnf(i_0_4, plain, (contains(X3,X2)|~equ(X1,X3)|~contains(X1,X2))).
cnf(i_0_1, plain, (equ(X1,X2)|contains(X2,esk1_2(X1,X2))|contains(X1,esk1_2(X1,X2)))).
cnf(i_0_2, plain, (equ(X1,X2)|~contains(X2,esk1_2(X1,X2))|~contains(X1,esk1_2(X1,X2)))).


