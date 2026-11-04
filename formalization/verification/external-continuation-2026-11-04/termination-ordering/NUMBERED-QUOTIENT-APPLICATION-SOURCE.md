# Literal application on the typed guarded quotient

Paper 06, lines 572–581, uses application tu in the arrow computability clause. This component supplies only literal application confinement and well-definedness of its representative code on the already checked guarded primary quotient.

The term is exactly AuxTerm.app. Subtype closure derives the result type's window membership from the confined function's arrow type. All four input terms in the congruence target are explicitly confined and have matching native dependent types and binder context. Equal representative codes are converted to actual WindowPrimary witnesses and lifted through its existing function and argument equivalence constructors.

The appArgument constructor here is primary equivalence, not positive reduction. No application-argument WindowStep is introduced. There is no numeric application decoder, primitive-recursion, C_tau, accessibility or ID1 claim.
