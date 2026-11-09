# Ranked word-row construction: source and interfaces

Source is `08-multivariate-collapse-comparison/paper.tex`, SHA256
`a4a8481437b8c7683ee8d82ec9e13e0a29af44110edcace0e9b0ef31b8fdaf0d`.
The intended endpoint is the unchanged printed `lem:row`; its closed
existential consumer is independent of arbitrary first-order BASE.

## Paid mathematics reused

* `PolynomialGraphCompletion.Row` is the literal source row, including integer
  coefficients, repeated raw names, and arbitrary admitted unary words.
* `OuterShiftNormalization` extracts final shift constants only under every
  original intermediate signed domain; it does not silently replace a string
  of shifts by its sum below that string's domain.
* `CounterLeaderExpansion` and `CounterLeaderCollision` provide the actual
  scheduled counter identity and exact aligned-input collision residuals.
* `CounterWordGuardCompletion.leaderWord` supplies literal generated source
  words, preserving their interior words and original raw arguments.
* `FullWordGuardCompletion` already computes exact pair guards and domains,
  with the selected maximum raw variable occurring only linearly.
* `ComparisonHistogramReplacement` and `ComparisonRankStepWellFounded`
  already prove finite reverse-rank replacement decrease. The row instance
  counts only top-level atoms, unlike the separate nested guard measure.

## Concrete remaining row compiler

For each current row, strip its final shifts and retain every original domain.
Ordinary range heads have row rank zero. Counter heads have their actual rank
in `3..D`; argument nodes are excluded from this top-level rank list.

Enumerate finite ordered partitions of the current ordinary values and
counter leaders. Each branch retains literal pair-comparison guards. The
`NamedMaximumComparison` target transports the accepted pair compiler into
L4's shared Boolean word-row AST, using original names only. Pair comparisons
not involving the selected maximum can remain literal rows independent of it.

The actual enumeration assigns each of the `n` current atoms every label in
`0..n-1` and retains all pair-order guards. For semantic coverage, label a
leader by the number of current leaders strictly smaller than it. Its own
occurrence proves that count is below `n`; finite-count monotonicity and a
strict witness prove that the resulting numerical labels have exactly the
actual leader order. This valuation-dependent labelling is only a witness
that one enumerated guard is true. The compiler itself enumerates all label
vectors and never computes a semantic leader value or queries guard truth.

Within each leader class, retain the current literal atoms and compute the
integer quantity `2*sum ordinary coefficients + sum counter coefficients`.
A separate coefficient-merging or representative-preference algorithm is
unnecessary for the following exact rewrites.

For a zero-leading class containing any nonzero ordinary atom, use the concrete
doubled counter expansion on every counter and cancel the common leader. All
ordinary atoms disappear, including when their aggregate coefficient was zero;
only positive-rank residual terms and integer corrections remain. Thus rank
zero strictly decreases.

For a counter-only zero-leading class, choose a least-rank original counter.
The actual collision identity rewrites each higher-rank counter as that common
least-rank counter plus its own upper residuals. Same-rank terms are equal as
whole counters. Their total coefficient is zero, so every common least-rank
term cancels. All newly emitted residual ranks strictly exceed the least rank;
all original class terms disappear. This proves the same top-level histogram
decrease without first merging equal-rank terms.

Repartition after every rewrite. The doubled identity is used only in the
proof: emit the undoubled residual coefficients and integer corrections, prove
their doubled equality, then cancel two in the integers. The actual child row
therefore preserves EXACT value, not just sign; it never accumulates a global
scaling factor. Each residual keeps the raw name and literal interior of the
original term which actually emitted it.

The current-word syntax supplies growth provenance after each rewrite. A
deleted maximum-variable word never labels a residual in a different raw
name. If no current nonlinear maximum-variable occurrence remains, retain
the exact row, now linear in that maximum. Otherwise, the greatest surviving
leader determines the sign after a computed common tail.

For this final estimate the stronger accepted residual bound
`t + sum residuals <= leaderPreimage` bounds the signed correction from a
counter's half-leader by its actual leader preimage. Every current generated
leader and preimage can pay a cofinality threshold at the common all-large
tail. Discrete Phi range gaps then dominate all smaller leader classes;
the existing quadratic growth bound pays the integer-linear and constant
error. This avoids introducing real logarithms. All chosen thresholds are
explicit sufficient tails, without a minimality or complexity claim.

## Closed consumer boundary

L4 owns the actual word-linear Presburger adapter, nonlinear residues and
closed raw-variable-count recursion. Its semantic parameters remain the
actual original words, never independent quantified values. Before using any
generated tail words, the closed algorithm must split the ORIGINAL current
formula into the all-large branch and finite branches substituting an original
raw variable. It must not evaluate a newly introduced negative-depth word
below its generated domain. Each finite, linear or all-large branch removes
one actual raw existential name.

R001 and R002 currently freeze supporting concrete identities/interfaces only.
The full finite row compiler, its effectivity, closed decision and level-two
source assembly remain pending until actual proofs and exact native gates.
