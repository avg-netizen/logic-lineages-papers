# Primary equivalence preserves arbitrary binder-aware support

Draft for review; no proof/export. Structural context/primary-class prerequisites for paper 06 lines 552–558 and 583–597.

The tuple/list target calibrates structural supportsArguments against universal support of every packed occurrence in the actual argumentList. ActualPrimarySupport and ActualArgumentPrimarySupport are iff for arbitrary type-indexed free-variable predicates P, not just a renaming range. Lambda uses liftPredicate P and application checks both components.

Primitive ordinary/numbered equivalence may permute base arguments and change equivalent heads. The list calibration and actual permutation membership equivalence transport support across that base permutation; repeated occurrences are not discarded or transformed into a set equality. Numbered labels/output types and ordered extras remain as in the actual constructors. Refl/symm/trans and tuple congruence use the logical iff in the same typed context. Head/window guards are retained; no stronger relation is used.

No step/mark support preservation, arbitrary reduction image closure, Acc/C stability, ID1 or global termination claim. Prior accepted files unchanged.
