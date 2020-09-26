% Group Theory example
% The universe is described as a group
% The group is conjectured to be abelian
% The following link should tell you for which sizes non-abelian groups exist for
% https://en.wikipedia.org/wiki/List_of_small_groups#List_of_small_non-abelian_groups
% Note that any prime sized group will be abelian, since they are cyclic and cyclic groups are abelian

fof(associative, axiom, (
    ! [A, B, C] : (f(f(A, B), C) = f(A, f(B, C)))
    )).

fof(identity, axiom, (
    ! [A] : ((f(A, e) = A) & (f(e, A) = A))
    )).

fof(inverse, axiom, (
    ! [A] : (? [B] : ((f(A, B) = e) & (f(B, A) = e)))
    )).

fof(abelian, conjecture, (
    ! [A, B] : (f(A, B) = f(B, A))
    )).
