%------------------------------------------------------------------------------
% File     : MED009+1 : TPTP v7.4.0. Released v3.2.0.
% Domain   : Medicine
% Problem  : Unsuccessful s1-qige27 treatment - next step
% Version  : [HLB05] axioms : Especial.
% English  : After unsuccessful treatment with single oral anti-diabetic for
%            patients with QI greater equal than 27 medical management moves
%            to next step.

% Refs     : [HLB05] Hommersom et al. (2005), Automated Theorem Proving for
%          : [Hom06] Hommersom (2006), Email to G. Sutcliffe
% Source   : [Hom06]
% Names    :

% Status   : Theorem
% Rating   : 0.29 v7.4.0, 0.12 v7.3.0, 0.14 v7.2.0, 0.17 v7.1.0, 0.00 v7.0.0, 0.07 v6.3.0, 0.08 v6.2.0, 0.18 v6.1.0, 0.36 v6.0.0, 0.25 v5.5.0, 0.54 v5.4.0, 0.52 v5.3.0, 0.57 v5.2.0, 0.36 v5.0.0, 0.35 v4.1.0, 0.44 v4.0.1, 0.47 v4.0.0, 0.50 v3.7.0, 0.33 v3.5.0, 0.25 v3.4.0, 0.33 v3.3.0, 0.67 v3.2.0
% Syntax   : Number of formulae    :   41 (   1 unit)
%            Number of atoms       :  201 (   0 equality)
%            Maximal formula depth :   12 (   6 average)
%            Number of connectives :  245 (  85   ~;  34   |;  51   &)
%                                         (   0 <=>;  75  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :   20 (   0 propositional; 1-2 arity)
%            Number of functors    :    1 (   1 constant; 0-0 arity)
%            Number of variables   :   96 (   0 sgn;  92   !;   4   ?)
%            Maximal term depth    :    1 (   1 average)
% SPC      : FOF_THM_RFO_NEQ

% Comments :
%------------------------------------------------------------------------------
fof(irreflexivity_gt,axiom,(
    ! [X] : ~ gt(X,X) )).

fof(transitivity_gt,axiom,(
    ! [X,Y,Z] :
      ( ( gt(X,Y)
        & gt(Y,Z) )
     => gt(X,Z) ) )).

fof(xorcapacity1,axiom,(
    ! [X0] :
      ( bcapacityne(X0)
      | bcapacityex(X0)
      | bcapacitysn(X0) ) )).

fof(xorcapacity2,axiom,(
    ! [X0] :
      ( ~ bcapacityne(X0)
      | ~ bcapacityex(X0) ) )).

fof(xorcapacity3,axiom,(
    ! [X0] :
      ( ~ bcapacityne(X0)
      | ~ bcapacitysn(X0) ) )).

fof(xorcapacity4,axiom,(
    ! [X0] :
      ( ~ bcapacityex(X0)
      | ~ bcapacitysn(X0) ) )).

fof(xorcondition1,axiom,(
    ! [X0] :
      ( conditionhyper(X0)
      | conditionhypo(X0)
      | conditionnormo(X0) ) )).

fof(xorcondition2,axiom,(
    ! [X0] :
      ( ~ conditionhyper(X0)
      | ~ conditionhypo(X0) ) )).

fof(xorcondition3,axiom,(
    ! [X0] :
      ( ~ conditionhyper(X0)
      | ~ conditionnormo(X0) ) )).

fof(xorcondition4,axiom,(
    ! [X0] :
      ( ~ conditionhypo(X0)
      | ~ conditionnormo(X0) ) )).

fof(insulin_effect,axiom,(
    ! [X0] :
      ( ! [X1] :
          ( ~ gt(X0,X1)
         => drugi(X1) )
     => ! [X1] :
          ( ~ gt(X0,X1)
         => ( uptakelg(X1)
            & uptakepg(X1) ) ) ) )).

fof(liver_glucose,axiom,(
    ! [X0,X1] :
      ( ~ gt(X0,X1)
     => ( uptakelg(X1)
       => ~ releaselg(X1) ) ) )).

fof(sulfonylurea_effect,axiom,(
    ! [X0] :
      ( ( ! [X1] :
            ( ~ gt(X0,X1)
           => drugsu(X1) )
        & ~ bcapacityex(X0) )
     => ! [X1] :
          ( ~ gt(X0,X1)
         => bsecretioni(X1) ) ) )).

fof(biguanide_effect,axiom,(
    ! [X0] :
      ( ! [X1] :
          ( ~ gt(X0,X1)
         => drugbg(X1) )
     => ! [X1] :
          ( ~ gt(X0,X1)
         => ~ releaselg(X1) ) ) )).

fof(sn_cure_1,axiom,(
    ! [X0] :
      ( ( ! [X1] :
            ( ~ gt(X0,X1)
           => bsecretioni(X1) )
        & bcapacitysn(X0)
        & qilt27(X0)
        & ! [X1] :
            ( gt(X0,X1)
           => conditionhyper(X1) ) )
     => ! [X1] :
          ( ~ gt(X0,X1)
         => conditionnormo(X1) ) ) )).

fof(sn_cure_2,axiom,(
    ! [X0] :
      ( ( ! [X1] :
            ( ~ gt(X0,X1)
           => ~ releaselg(X1) )
        & bcapacitysn(X0)
        & ~ qilt27(X0)
        & ! [X1] :
            ( gt(X0,X1)
           => conditionhyper(X1) ) )
     => ! [X1] :
          ( ~ gt(X0,X1)
         => conditionnormo(X1) ) ) )).

fof(ne_cure,axiom,(
    ! [X0] :
      ( ( ( ! [X1] :
              ( ~ gt(X0,X1)
             => ~ releaselg(X1) )
          | ! [X1] :
              ( ~ gt(X0,X1)
             => uptakepg(X1) ) )
        & bcapacityne(X0)
        & ! [X1] :
            ( ~ gt(X0,X1)
           => bsecretioni(X1) )
        & ! [X1] :
            ( gt(X0,X1)
           => conditionhyper(X1) ) )
     => ! [X1] :
          ( ~ gt(X0,X1)
         => conditionnormo(X1) ) ) )).

fof(ex_cure,axiom,(
    ! [X0] :
      ( ( ! [X1] :
            ( ~ gt(X0,X1)
           => uptakelg(X1) )
        & ! [X1] :
            ( ~ gt(X0,X1)
           => uptakepg(X1) )
        & bcapacityex(X0)
        & ! [X1] :
            ( gt(X0,X1)
           => conditionhyper(X1) ) )
     => ! [X1] :
          ( ~ gt(X0,X1)
         => ( conditionnormo(X1)
            | conditionhypo(X1) ) ) ) )).

fof(xorstep1,axiom,(
    ! [X0] :
      ( s0(X0)
      | s1(X0)
      | s2(X0)
      | s3(X0) ) )).

fof(xorstep2,axiom,(
    ! [X0] :
      ( ~ s0(X0)
      | ~ s1(X0) ) )).

fof(xorstep3,axiom,(
    ! [X0] :
      ( ~ s0(X0)
      | ~ s2(X0) ) )).

fof(xorstep4,axiom,(
    ! [X0] :
      ( ~ s0(X0)
      | ~ s3(X0) ) )).

fof(xorstep5,axiom,(
    ! [X0] :
      ( ~ s1(X0)
      | ~ s2(X0) ) )).

fof(xorstep6,axiom,(
    ! [X0] :
      ( ~ s1(X0)
      | ~ s3(X0) ) )).

fof(xorstep7,axiom,(
    ! [X0] :
      ( ~ s2(X0)
      | ~ s3(X0) ) )).

fof(normo,axiom,(
    ! [X0] :
      ( ! [X1] :
          ( ~ gt(X0,X1)
         => conditionnormo(X1) )
     => ( ( ! [X1] :
              ( ~ gt(X0,X1)
             => bsecretioni(X1) )
          & bcapacitysn(X0)
          & qilt27(X0)
          & ! [X1] :
              ( gt(X0,X1)
             => conditionhyper(X1) ) )
        | ( ! [X1] :
              ( ~ gt(X0,X1)
             => ~ releaselg(X1) )
          & bcapacitysn(X0)
          & ~ qilt27(X0)
          & ! [X1] :
              ( gt(X0,X1)
             => conditionhyper(X1) ) )
        | ( ( ! [X1] :
                ( ~ gt(X0,X1)
               => ~ releaselg(X1) )
            | ! [X1] :
                ( ~ gt(X0,X1)
               => uptakepg(X1) ) )
          & bcapacityne(X0)
          & ! [X1] :
              ( ~ gt(X0,X1)
             => bsecretioni(X1) )
          & ! [X1] :
              ( gt(X0,X1)
             => conditionhyper(X1) ) )
        | ( ! [X1] :
              ( ~ gt(X0,X1)
             => uptakelg(X1) )
          & ! [X1] :
              ( ~ gt(X0,X1)
             => uptakepg(X1) )
          & bcapacityex(X0)
          & ! [X1] :
              ( gt(X0,X1)
             => conditionhyper(X1) ) ) ) ) )).

fof(step1,axiom,(
    ! [X0] :
      ( ( s1(X0)
        & qilt27(X0) )
     => drugsu(X0) ) )).

fof(step2,axiom,(
    ! [X0] :
      ( ( s1(X0)
        & ~ qilt27(X0) )
     => drugbg(X0) ) )).

fof(step3,axiom,(
    ! [X0] :
      ( s2(X0)
     => ( drugbg(X0)
        & drugsu(X0) ) ) )).

fof(step4,axiom,(
    ! [X0] :
      ( s3(X0)
     => ( ( drugi(X0)
          & ( drugsu(X0)
            | drugbg(X0) ) )
        | drugi(X0) ) ) )).

fof(bgcomp,axiom,(
    ! [X0] :
      ( drugbg(X0)
     => ( ( s1(X0)
          & ~ qilt27(X0) )
        | s2(X0)
        | s3(X0) ) ) )).

fof(sucomp,axiom,(
    ! [X0] :
      ( drugsu(X0)
     => ( ( s1(X0)
          & qillt27(X0) )
        | s2(X0)
        | s3(X0) ) ) )).

fof(insulincomp,axiom,(
    ! [X0] :
      ( drugi(X0)
     => s3(X0) ) )).

fof(insulin_completion,axiom,(
    ! [X0] :
      ( ( ! [X1] :
            ( ~ gt(X0,X1)
           => uptakelg(X1) )
        | ! [X1] :
            ( ~ gt(X0,X1)
           => uptakepg(X1) ) )
     => ! [X1] :
          ( ~ gt(X0,X1)
         => drugi(X1) ) ) )).

fof(uptake_completion,axiom,(
    ! [X0,X1] :
      ( ~ gt(X0,X1)
     => ( ~ releaselg(X1)
       => uptakelg(X1) ) ) )).

fof(su_completion,axiom,(
    ! [X0] :
      ( ! [X1] :
          ( ~ gt(X0,X1)
         => bsecretioni(X1) )
     => ( ! [X1] :
            ( ~ gt(X0,X1)
           => drugsu(X1) )
        & ~ bcapacityex(X0) ) ) )).

fof(bg_completion,axiom,(
    ! [X0] :
      ( ! [X1] :
          ( ~ gt(X0,X1)
         => ~ releaselg(X1) )
     => ! [X1] :
          ( ~ gt(X0,X1)
         => drugbg(X1) ) ) )).

fof(trans_ax1,axiom,(
    ! [X0] :
      ( ( s0(X0)
        & ~ ! [X1] :
              ( ~ gt(X0,X1)
             => conditionnormo(X1) ) )
     => ? [X1] :
          ( ~ gt(X0,X1)
          & s1(X1)
          & ! [X2] :
              ( gt(X1,X2)
             => conditionhyper(X2) ) ) ) )).

fof(trans_ax2,axiom,(
    ! [X0] :
      ( ( s1(X0)
        & ~ ! [X1] :
              ( ~ gt(X0,X1)
             => conditionnormo(X1) ) )
     => ? [X1] :
          ( ~ gt(X0,X1)
          & s2(X1)
          & ! [X2] :
              ( gt(X1,X2)
             => conditionhyper(X2) )
          & ( bcapacityne(X1)
            | bcapacityex(X1) ) ) ) )).

fof(trans_ax3,axiom,(
    ! [X0] :
      ( ( s2(X0)
        & ~ ! [X1] :
              ( ~ gt(X0,X1)
             => conditionnormo(X1) ) )
     => ? [X1] :
          ( ~ gt(X0,X1)
          & s3(X1)
          & ! [X2] :
              ( gt(X1,X2)
             => conditionhyper(X2) )
          & bcapacityex(X1) ) ) )).
%------------------------------------------------------------------------------
fof(transs1s2_qige27,conjecture,
    ( ( s1(n0)
      & ! [X0] :
          ( gt(n0,X0)
         => conditionhyper(X0) )
      & ~ bcapacitysn(n0)
      & ~ qilt27(n0) )
   => ? [X0] :
        ( ~ gt(n0,X0)
        & s2(X0)
        & ! [X1] :
            ( gt(X0,X1)
           => conditionhyper(X1) )
        & ( bcapacityne(X0)
          | bcapacityex(X0) ) ) )).

%------------------------------------------------------------------------------
