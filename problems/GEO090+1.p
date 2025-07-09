%--------------------------------------------------------------------------
% File     : GEO090+1 : TPTP v9.0.0. Released v2.4.0.
% Domain   : Geometry (Oriented curves)
% Problem  : Meeting point of curves on a subcurve
% Version  : [EHK99] axioms.
% English  : If a point P is a meeting point of two curves and lies on a
%            sub-curve of one of the two curves then P is also meeting point
%            of the sub-curve and the other curve.

% Refs     : [KE99]  Kulik & Eschenbach (1999), A Geometry of Oriented Curv
%          : [EHK99] Eschenbach et al. (1999), Representing Simple Trajecto
% Source   : [KE99]
% Names    : Corollary 2.12 [KE99]

% Status   : Theorem
% Rating   : 0.88 v9.0.0, 0.86 v7.5.0, 0.91 v7.4.0, 0.80 v7.3.0, 0.79 v7.1.0, 0.74 v7.0.0, 0.83 v6.4.0, 0.88 v6.3.0, 0.79 v6.2.0, 0.84 v6.1.0, 0.87 v6.0.0, 0.91 v5.5.0, 0.93 v5.4.0, 0.89 v5.3.0, 0.93 v5.2.0, 0.95 v5.1.0, 1.00 v3.2.0, 0.91 v3.1.0, 0.89 v2.7.0, 1.00 v2.4.0
% Syntax   : Number of formulae    :   17 (   1 unt;   0 def)
%            Number of atoms       :   71 (  10 equ)
%            Maximal formula atoms :   12 (   4 avg)
%            Number of connectives :   58 (   4   ~;   9   |;  23   &)
%                                         (   9 <=>;  13  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   12 (   7 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    8 (   7 usr;   0 prp; 1-3 aty)
%            Number of functors    :    1 (   1 usr;   0 con; 2-2 aty)
%            Number of variables   :   57 (  48   !;   9   ?)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%--------------------------------------------------------------------------
%----Include simple curve axioms
include('Axioms/GEO004+0.ax').
%--------------------------------------------------------------------------
fof(corollary_2_12,conjecture,
    ! [C1,C2,Cpp,P] :
      ( ( part_of(C2,C1)
        & incident_c(P,C2)
        & meet(P,C1,Cpp) )
     => meet(P,C2,Cpp) ) ).

%--------------------------------------------------------------------------
