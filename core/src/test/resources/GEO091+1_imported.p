%--------------------------------------------------------------------------
% File     : GEO091+1 : TPTP v7.4.0. Released v2.4.0.
% Domain   : Geometry (Oriented curves)
% Problem  : Two points determine subcurve
% Version  : [EHK99] axioms.
% English  : Two distinct points on an open curve uniquely determine the
%            sub-curve connecting these points

% Refs     : [KE99]  Kulik & Eschenbach (1999), A Geometry of Oriented Curv
%          : [EHK99] Eschenbach et al. (1999), Representing Simple Trajecto
% Source   : [KE99]
% Names    : Theorem 2.13 [KE99]

% Status   : Unknown
% Rating   : 1.00 v2.4.0
% Syntax   : Number of formulae    :   17 (   1 unit)
%            Number of atoms       :   76 (  12 equality)
%            Maximal formula depth :   14 (   7 average)
%            Number of connectives :   64 (   5   ~;   9   |;  28   &)
%                                         (   9 <=>;  13  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    8 (   0 propositional; 1-3 arity)
%            Number of functors    :    1 (   0 constant; 2-2 arity)
%            Number of variables   :   58 (   0 sgn;  47   !;  11   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_UNK_RFO_SEQ

% Comments :
%--------------------------------------------------------------------------
%----Include simple curve axioms
fof(part_of_defn,axiom,
    ( ! [C,C1] :
        ( part_of(C1,C)
      <=> ! [P] :
            ( incident_c(P,C1)
           => incident_c(P,C) ) ) )).

fof(sum_defn,axiom,
    ( ! [C,C1,C2] :
        ( C = sum(C1,C2)
      <=> ! [Q] :
            ( incident_c(Q,C)
          <=> ( incident_c(Q,C1)
              | incident_c(Q,C2) ) ) ) )).

fof(end_point_defn,axiom,
    ( ! [P,C] :
        ( end_point(P,C)
      <=> ( incident_c(P,C)
          & ! [C1,C2] :
              ( ( part_of(C1,C)
                & part_of(C2,C)
                & incident_c(P,C1)
                & incident_c(P,C2) )
             => ( part_of(C1,C2)
                | part_of(C2,C1) ) ) ) ) )).

fof(inner_point_defn,axiom,
    ( ! [P,C] :
        ( inner_point(P,C)
      <=> ( incident_c(P,C)
          & ~ end_point(P,C) ) ) )).

fof(meet_defn,axiom,
    ( ! [P,C,C1] :
        ( meet(P,C,C1)
      <=> ( incident_c(P,C)
          & incident_c(P,C1)
          & ! [Q] :
              ( ( incident_c(Q,C)
                & incident_c(Q,C1) )
             => ( end_point(Q,C)
                & end_point(Q,C1) ) ) ) ) )).

fof(closed_defn,axiom,
    ( ! [C] :
        ( closed(C)
      <=> ~ ( ? [P] : end_point(P,C) ) ) )).

fof(open_defn,axiom,
    ( ! [C] :
        ( open(C)
      <=> ? [P] : end_point(P,C) ) )).

fof(c1,axiom,
    ( ! [C,C1] :
        ( ( part_of(C1,C)
          & C1 != C )
       => open(C1) ) )).

fof(c2,axiom,
    ( ! [C,C1,C2,C3] :
        ( ( part_of(C1,C)
          & part_of(C2,C)
          & part_of(C3,C)
          & ? [P] :
              ( end_point(P,C1)
              & end_point(P,C2)
              & end_point(P,C3) ) )
       => ( part_of(C2,C3)
          | part_of(C3,C2)
          | part_of(C1,C2)
          | part_of(C2,C1)
          | part_of(C1,C3)
          | part_of(C3,C1) ) ) )).

fof(c3,axiom,
    ( ! [C] :
      ? [P] : inner_point(P,C) )).

fof(c4,axiom,
    ( ! [C,P] :
        ( inner_point(P,C)
       => ? [C1,C2] :
            ( meet(P,C1,C2)
            & C = sum(C1,C2) ) ) )).

fof(c5,axiom,
    ( ! [C,P,Q,R] :
        ( ( end_point(P,C)
          & end_point(Q,C)
          & end_point(R,C) )
       => ( P = Q
          | P = R
          | Q = R ) ) )).

fof(c6,axiom,
    ( ! [C,P] :
        ( end_point(P,C)
       => ? [Q] :
            ( end_point(Q,C)
            & P != Q ) ) )).

fof(c7,axiom,
    ( ! [C,C1,C2,P] :
        ( ( closed(C)
          & meet(P,C1,C2)
          & C = sum(C1,C2) )
       => ! [Q] :
            ( end_point(Q,C1)
           => meet(Q,C1,C2) ) ) )).

fof(c8,axiom,
    ( ! [C1,C2] :
        ( ? [P] : meet(P,C1,C2)
       => ? [C] : C = sum(C1,C2) ) )).

fof(c9,axiom,
    ( ! [C,C1] :
        ( ! [P] :
            ( incident_c(P,C)
          <=> incident_c(P,C1) )
       => C = C1 ) )).
%--------------------------------------------------------------------------
fof(theorem_2_13,conjecture,
    ( ! [C,C1,C2] :
        ( ( part_of(C1,C)
          & part_of(C2,C)
          & open(C)
          & ? [P,Q] :
              ( P != Q
              & end_point(P,C1)
              & end_point(P,C2)
              & end_point(Q,C1)
              & end_point(Q,C2) ) )
       => C1 = C2 ) )).

%--------------------------------------------------------------------------
