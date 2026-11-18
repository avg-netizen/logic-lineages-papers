# Source map: successful full-call covariance

The statement used is the unnumbered paragraph immediately following
`def:application` in ordering.tex: a successful full call commutes with
capture-avoiding substitution, because the branch inspecting an original
variable is excluded by success. The same identity is invoked in the proof of
`lem:structural-stability`. This packet proves the identity for the locally
nameless auxiliary presentation; it does not discharge that numbered lemma,
which also requires the actual comparison derivations and context closure.

FreeSubstitution maps typed free names to outside terms simultaneously, using
`shift d 0` at depth d, preserving all original head/base/extras nodes. Bound
indices in images are allowed. No fresh-name selection algorithm is used.
The presentation has not been related to the earlier named syntax modulo
alpha; that bridge remains separate and unclaimed.

ShiftCancellation and ShiftArgsCancellation specify actual binder-block
removal after insertion past the entire block. FreeShift and FreeShiftArgs
specify insertion under an additional binder segment. ParallelComposition and
ParallelArgsComposition state full finite-list substitution composition on
all raw terms, not merely empty substitution or a particular closed example.
AnnotationPreserves derives raw annotation preservation from typed images.
SuccessfulCallCovariance applies the actual `apply` to mapped source and
arguments and proves the exact mapped result from original success.

The final assumptions include typing of source, images and argument tuple;
none asserts anything about the computed output. A stronger raw helper may
use only type-exact images and original success, but the published target
internally obtains image type exactness from Typed proofs.
