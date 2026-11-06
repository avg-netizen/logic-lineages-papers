# Paper 02 finite comparison and bounded-vector source contracts

The source is `02-exponential-comparison/paper.tex`, labels
`thm:finite-bare-hardness` and `thm:bounded-bare-vectors`. The manuscript and all
previous accepted source definitions remain unchanged. The new targets are in
`LogicLineages/ComputabilityKnowledge/BareHardnessCompletion/Targets.lean`.

## Finite depth-two comparison

`ScalarCode` is the standard computably encoded triple consisting of the common
ground-name arity and the two literal expression codes. `ScalarDomain` requires
both codes to represent `PositiveExpression.Expr (Fin d)` with exponential
nesting depth at most two. These expressions contain precisely one, positive
ground variables, addition, and `E(a,b) = 2^a*b`. Arity zero is retained.

`ScalarComparison norm weak` is defined by an existential witness for these
literal source expressions, their exact codes, their depth bounds, and their
original WW comparison. The source comparison is over all admissible
substitutions on the occurring ground names. The two terms share the same
substitution. `norm = true` uses the actual ordinal norm; `weak = false` uses
strict comparison. Neither semantic predicate is defined by a search program.
Malformed or over-depth input is outside the restricted problem.

`Pi01Complete S` means that the complement of `S` is recursively enumerable and
that the complement of every recursively enumerable predicate on naturals
has a total computable many-one reduction to `S`. The target therefore requires
the complete co-RE classification, not merely a reduction from one undecidable
problem. Standard `Primcodable` product and list codes are used throughout.

`ScalarHardness` separately requires that every output of each reduction is in
`ScalarDomain`, including outputs corresponding to nonsolutions. The same
reduction establishes value and norm comparison. `PositiveSourceFacts` retains
the printed positivity, finiteness, actual-norm equality and membership in
every `C_i`, `i >= 1`, on the genuine occurring-name substitution domain.

The accepted Diophantine representation is used with one fixed representing
polynomial for each fixed RE predicate. Its explicit specialization in the
natural input is computable and well formed for every input. The established
nonnegative-polynomial comparison compiler performs the literal `X_i-1`
domain conversion, finite circuit translation and sum-of-squares construction.
Its strict output is `(V,U)`; its weak output is `(V+1,U)`. No procedure selecting
a polynomial from an extensional proof is asserted.

The upper-bound proof must account for both invalid syntax and semantic
counterexamples. The complement of an existing counterexample predicate alone
would incorrectly admit malformed codes. The frozen semantic domain excludes
this error; `ScalarValidation` requires a computable exact recognizer.

## Bounded two-component source vectors

`VectorCode` retains the common arity and both literal lists of source-term
codes. `BoundedSourcePair` requires the source `CVector` and `VectorBoundedNorm`
predicates for both vectors. `HigherDepthTwo` requires exactly two components
and an embedded finite depth-two expression in component one.

`VectorComparison weak` adds exactly `VectorLE` or `VectorLT` to this domain.
Strict comparison is strict at component zero and weak at every positive
component, with the existing zero extension. The original relation is not
replaced by a different vector order.

The literal construction remains

\[
R=U+V+1,\qquad H=\psi(\omega\cdot R+g),\qquad
(H,V+1),\ (H,U),\ (H+1,U),
\]

where the accepted `WWFiniteEnvelope` supplies the paper's source-tree size,
positive affine control and unchanged bound `g=5b`. Existing padding theorems
prove class membership and bounded norms uniformly over original admissible
substitutions. `vectorProgram` calls the actual proved padding program on the
strict scalar output, reversing `(V,U)` into its required arguments `(U,V)`.

`VectorHardness` requires a total computable reduction from every RE complement,
with every output certified in the restricted genuine vector domain. It proves
both order symbols. `VectorUndecidable` excludes even a total computable Boolean
procedure required to answer correctly only on those valid bounded inputs;
its answers on malformed inputs are unrestricted. No co-RE classification of
arbitrary ordinal-vector comparison is part of the printed theorem or target.

## Scope and preservation

These two source obligations do not decide arbitrary finite-valued collapse
terms, prove the broader consumer corollary, or complete paper 08's first-order
BASE or polynomial-word comparison chain. Existing finite-source comparison
and uniform kernel-separation results remain preserved. Target promotion is
conditional on the original serialized native gate and actual transitive
standard-axiom audit; a successful focused closure does not claim a full-root
or remote-CI build.
