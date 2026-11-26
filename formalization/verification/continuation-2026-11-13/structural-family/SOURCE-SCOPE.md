# Candidate generic-family obstruction (unverified)

The printed paper06 lemma `lem:structural` (paper.tex lines 275–278) asserts
scanner substitution at a natural coherent constructor family. Its displayed
constructor coherence equation is weakening coherence, matching
`CoherentConstructorLattice.Good`; that predicate contains no cross-type tuple law.

The new specification copies the conditions and equality of
`ActualLimitSubstitutionTargets.ScannerSubstitution`, but substitutes an arbitrary
`M : Constructors input` for the actual fixed point. The input is explicitly
source zero and target successor, so zero is an admitted head and ground/ground-arrow
types occur. The proposed family is constant top at ground and bottom at arrows.
It is intended to satisfy monotonicity and weakening coherence.

Candidate witness: q is the free variable x of type ground→ground. Substitute
closed marked zero retagged to ground→ground, with empty base and extra lists.
Take both masks false, the source environment equal to that term's interpretation
(bottom), and apply the scanner to one ground argument. The variable branch
uses bottom's actual full table, hence returns bottom. The substituted marked
branch consults the ground result constructor, hence returns top. Ground top
and bottom differ in their availability bit, even without observation bits.
Confinement, environment agreement and protected compatibility are to be proved,
not removed from the target. Native checking has not occurred.

This does not refute any accepted theorem: the existing substitution targets
quantify over `SourceConstructorIteration.limit`, whose extra full-tuple equation
is established by `ActualLimitInterpretationTargets.FullTupleEquation`. Generic
monotonicity/naturality and structural-renaming results are unaffected. The
numbered structural lemma is already pending. No register or manuscript change
is made. The specification is a negative supporting result, not a repair to the
printed statement and not an authorization to alter its assumptions.
