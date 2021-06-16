%------------------------------------------------------------------------------
% File     : ALG212+1 : TPTP v7.4.0. Released v3.2.0.
% Domain   : General Algebra (Median Algebra)
% Problem  : Distributivity, long version
% Version  : [VMURL] axioms.
% English  :

% Refs     : [VMURL] Veroff & McCune (URL), First-order Proof of a Median A
% Source   : [VMURL]
% Names    : dist_long [VMURL]

% Status   : Theorem
% Rating   : 1.00 v3.2.0
% Syntax   : Number of formulae    :    5 (   5 unit)
%            Number of atoms       :    5 (   5 equality)
%            Maximal formula depth :    6 (   4 average)
%            Number of connectives :    0 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    1 (   0 propositional; 2-2 arity)
%            Number of functors    :    1 (   0 constant; 3-3 arity)
%            Number of variables   :   17 (   0 sgn;  17   !;   0   ?)
%            Maximal term depth    :    3 (   2 average)
% SPC      : FOF_THM_RFO_PEQ

% Comments :
%------------------------------------------------------------------------------
%----Include median algebra axioms
fof(majority,axiom,(
    ! [X,Y] : f(X,X,Y) = X )).

fof(permute1,axiom,(
    ! [X,Y,Z] : f(X,Y,Z) = f(Z,X,Y) )).

fof(permute2,axiom,(
    ! [X,Y,Z] : f(X,Y,Z) = f(X,Z,Y) )).

fof(associativity,axiom,(
    ! [W,X,Y,Z] : f(f(X,W,Y),W,Z) = f(X,W,f(Y,W,Z)) )).

%------------------------------------------------------------------------------
fof(dist_long,conjecture,(
    ! [U,W,X,Y,Z] : f(f(X,Y,Z),U,W) = f(f(X,U,W),f(Y,U,W),f(Z,U,W)) )).

%------------------------------------------------------------------------------
