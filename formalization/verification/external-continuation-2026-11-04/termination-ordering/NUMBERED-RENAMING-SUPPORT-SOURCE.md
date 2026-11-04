# Binder-aware support and exact renaming-image existence

Draft for exact review; no proof/export. Structural fresh-context prerequisite for paper 06 lines 583–597.

VariablePredicate is type-indexed. supports traverses the actual term/tuple syntax: variables test P, bottom has no free variables, application checks both subterms, ordinary checks base, numbered checks base and extras, and lambda uses liftPredicate P. The lift permits newly bound here and tests P on there v. It therefore excludes an outer fresh variable at its shifted position under every binder, without excluding bound variables.

ActualLiftRange calibrates the range of the actual lifted renaming against liftPredicate(rangePredicate rho), at every typed variable. Term and tuple targets then state support by the range exactly iff the whole syntax is a literal renamed source, with complete types preserved. Maps may be noninjective; preimages need only exist, not be unique. Numbered annotations/labels/heads and argument order are unchanged by this representation. It neither assumes nor proves relation preservation.

For weakening, the predicate is exactly external-fresh-variable absence with correct binder shifting. It is not the false binder-insensitive property that no here occurs anywhere. Abs/Select/beta image closure will require separate support invariance arguments; they are not part of these targets. No primary/step preservation, Acc/C stability, ID1 or global theorem. Accepted bytes unchanged.
