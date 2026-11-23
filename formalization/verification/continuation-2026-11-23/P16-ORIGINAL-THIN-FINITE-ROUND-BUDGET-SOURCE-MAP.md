# Paper 16: actual physical length exhaustion and terminal member closure (thin)

Original sparse proof route: Paper 16 (T), sections/ordinals.tex:113–127;
and the previously developed physical SparseRoundBudget, SparseRoundCharge,
SparseRoundExhaustion, SparseFuelBudget and SparseMembersClosure modules.
This packet does not replace original programs or old closed results.
It eliminates the unrelated historical PrimaryMonotonicity/PrimaryUncoveredCount
import routes to Mathlib Hydra by using actual thin syntax and arithmetic
on the same physical rounds and member callback.

**Identity/scope.** The selected E is a single held Program4 on both
rounds. All original rounds, members, poolLength, actual membership,
and literal ordered vertex tapes are retained. The thin count counts
uncovered occurrences, not a set cardinality; duplicates are kept.
The budget remains the original disjunction of backwards membership
inclusion or elapsed-plus-uncovered-count ≤ actual allowance. No
equality of reached list codes is asserted.

1. **Round growth/strict.** Original adjacent persistence and
   round-on-original-vertices inclusion let an actual new member
   force strict decrease by the exact InternalStrictDecrease premise.
   Round alternative quantifies every real member of the actual next
   round, or pays the original strict decrease. Existing thin stable
   successor handles the already pre-fixed case.
2. **Arithmetic and finite induction.** The original eight-object-slot
   natural induction motive is retained; choosing intermediate actual
   rounds/counts uses real program existence. The exact CountLengthBound
   input pays the earliest count bounded by actual original length.
   At elapsed=length, arithmetic exhaustion and no-negative-count
   force reverse inclusion, with genuine before/after reports.
3. **Edge and pre-fixed at the true output.** The actual members
   callback exposes its physical length round; one genuine next
   directed extension and stability yield actual edge destination
   membership, for a target among the same vertices.
   ThinActualMembersPrefixedProof also opens an actual next pass on the
   physical reached pool and pays the existing thin prefixed formula,
   with no externally supplied fuel, next list, or pre-fixed witness.

Three checked or separately supplied proof inputs remain visible:
ExactRetainedPredecessor on actual original filter, actual
InternalStrictDecrease, and actual CountLengthBound on same count
and poolLength. This packet neither uses numerical correctness as
open reflection nor proves all-ground minima equality or arbitrary
representative compatibility. Original target code and manuscript
unaltered. These are source only until native checks pass.

Serial cuts: RoundBudgetChecks, RoundAlternativeChecks, RoundChargeChecks,
RoundExhaustionChecks, FuelBudgetSyntaxProof, FuelBudgetChecks (includes
Core+Induction), MembersClosureChecks, ActualMembersPrefixedProof.

Exact frozen recut and retained thin premise SHA256 pins:
~~~text
be1dc5091a21f8d7b802198579fc31892e3b42eed48dd167e094ea6ab69e88c5  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalThinRoundBudgetChecks.lean
066584eb2771600742d38f91dfbb50ba8daca246207c7bedd058f5482507c60d  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalThinRoundBudgetTargets.lean
3eca6142f4845fbc00e20e69237377bfa195e72e011ff687527bcdae17b38dad  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalThinRoundAlternativeChecks.lean
7fc02dd875ec6c02d43b7a3d40c9842600f4ac862148cad3004900aacb4ba371  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalThinRoundAlternativeTargets.lean
250d7a9d25eb6e6953ae97b927cf5daa321cf31989be3b8ed42e432b1d05fc1f  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalThinRoundChargeArithmeticProof.lean
5bfe694e0dc484de3467793c60f5bd94c6e4353673c2efc42b5c17f2064607d7  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalThinRoundChargeChecks.lean
a497b227f3727e49d4133d3161f032812a7f12878e151f6ebb46813dca846b01  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalThinRoundChargeTargets.lean
2fe857aa95f12e4889401ceef9e5a5a9f73e2edb0bbf7daa258ca4b3464c372f  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalThinRoundExhaustionArithmeticProof.lean
4cc0c8f1e47b429cdf0d8397bb65d412fb86775127ccf9a0a0bafcfbcc10e11a  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalThinRoundExhaustionChecks.lean
eeeac7e9242acfc7ef2932fde9553c7598e929bf99cf00926e414fc48ca0964d  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalThinRoundExhaustionTargets.lean
8ebfd0d6a6deecb422b9d1c425b543ed6e494f07a9cfc6c8dc75261a708e2df9  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalThinFuelBudgetChecks.lean
bc2a005767aa00f4c142d43ed3b08e98c950785af11e1cc88b1a4222e525e3ce  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalThinFuelBudgetCoreProof.lean
27686715d944884359589e61912c98fccf484af8d24f1bbbdcfb832b03321c4c  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalThinFuelBudgetInductionProof.lean
3ce7ddbd21ef45e141750fd10160fb3d5ce54fd69573b2348458bf0614506393  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalThinFuelBudgetSyntaxProof.lean
bb39e182bf07a2080cbc351f0d2140006d48b467a373dbe169c8cecbd08ed493  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalThinFuelBudgetTargets.lean
e7d4e699b63eb87e31c67a7991718fccbed3fe8bb0c34cd184a476bc019e280e  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalThinMembersClosureChecks.lean
05bfb91d0a0399097ef7eb62dd8d3b2ad594a08feb6db5814a193911ecd487c2  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalThinMembersClosureTargets.lean
a30497514ee2ff1ee16cfd36ae6feced40568ab9dc613b4d9b5c8ce207ffa6d3  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalThinActualMembersPrefixedProof.lean
0e306cec4baf33316604b5ab26c851e44e0a2432b4223282b18b1568bb79014a  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalThinRoundStabilityChecks.lean
c6ba738ef3c902fc5b2467b2bf4918fc725fc209fb92b1529bfe16a4a9124e78  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalThinUncoveredCountTargets.lean
3f3312792417309ebe7381bb0b796621d8f02f2644da8e74f7ad2c02347abc14  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalScratchInclusionThinProof.lean
526aa249902b4e4bf00f45bee770bdcdc9f9b39c2dc341778834600b7f8bf1b5  16-persistent-marking-termination-ordering/sections/ordinals.tex
~~~
