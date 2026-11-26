# Concrete charge of one actual selected zero-class rewrite

Paper 17, [arithmetic.tex](../../../17-permitted-control-canonical-comparison/sections/arithmetic.tex):
130–162 selects the original zero class and moves the higher prefixes to
the least surviving input. Lines 164–194 define the finite charge and
state `lem:inner-termination`: neither summand increases and the sum
strictly decreases. This packet applies that existing abstract theorem
to the exact concrete witness, once its separate gate passes.

The hypotheses are verbatim those of `ExactConcreteZeroClassAssembly`.
In particular the reads are the original lifted bounded reads, their
actual normalization and aligned annotations; the class is actual, the
original doubled leading sum is zero, and the same Ready/TransferReady
guards supply the selected classification and pair domains. No rank
positivity, maximum class, inequality, chosen witness, or abstract
replacement premise is added. The existential moved/ledger/anchor
witnesses and the exact finite column equations are preserved.

The source is literally `rankedRow r constant raw`. The output is
literally `concreteRow f C r constant xs annotations moved` for the same
actual moved list, not another row with equivalent charge. The existing
`InnerTerminationProof.fullInnerTermination`, instantiated at
`ValueKey r` and `NONote × NONote`, consumes the exact
`ZeroClassReplacement` supplied by assembly and gives the two weak
inequalities and the strict total inequality together. No new
normalization-loop result, search termination, or numbered promotion.

This is an authored source-only draft. Acceptance requires the concrete
assembly gate and a fresh exact gate of
`ActualZeroClassConcreteChargeStatementChecks`.
