# Item 2: "a seed in its own cover pool is a member of its class" — what is derivable and what is blocked

Fable B, 27 November 2026. File names without a path are under `LogicLineages/PersistentMarking/`.

## The law splits in two

The installed least program is
`memoFilteredLeast C Base s = guardedLeast (headerLeast (fullAuxiliaryDecorator (packedLeastOn C (recursiveTypedMemo Base) s)))`
and `packedLeastOn C E s = branch contextOption 0 (scratchMinimum (members E (poolAtSeed C s), ctx, ty, seed))`.

**(a) Member from pool occurrence — frozen, not proved, not blocked.**
`Paper16AccessibilityMilestoneSeedMemberLeastTargetsV2.SeedMemberLeast` (sha256
`4e4eb17c5f9ea79a4750f81651093ab3087b80ae6b4096f4c0465a9a8b21ff2b`, compiled in receipt
`1795778103135904967-942357`): from a successor of `contextOption`, the pool reported by
`poolAtSeed C s`, and `memberGraph pool seed`, the program `packedLeastOn C E s` returns a
successor. Every program on this path is visible code:
`members` = `rounds E` at fuel `poolLength pool` (`NumberedWindowInternalSparseDirectedRoundsDefinitions.lean`),
`roundBase`/`roundStep` = `pass` (`listRec` over the pool, `…DirectedFilterDefinitions.lean`),
`scan` = `listRec` over the seen list with `scanStep` (`…DirectedSeenDefinitions.lean`: "Equality is
sufficient; otherwise exact-one acceptance of E"), `scratchMinimum` = `listRec` with `minimumStep`.
The seed survives every round by the equality clause, independently of the edge program `E`.
The control flow is not shape-determined in one step (the fuel and both lists are open), but it is
inductive: one natural induction over the fuel, a list induction over the pool inside `pass`, a list
induction over the seen list inside `scan`, and a totality lemma for `scratchMinimum` on a list with
an occurrence (the existing `exact_OpenOrderedMinimumStep` / `exact_OpenScratchMinimumCons` are the
elimination direction only). I did not write this derivation; it is three nested inductions with
their renaming lemmas, comparable to the J-union proof. The statement has not been validated by a
proof, so treat it as a proposed target.

The other two hypotheses of (a) are available for K1/K2: `contextOption` returns a successor at the
context of an admitted address, because the address's own self-least report unfolds
(`exact_OpenAtomicLeastReport`, `exact_OpenLiteralHeaderLeastReport`, then
`exact_OpenPackedLeastPoolOccurrence`, which yields "an existential nonzero context tag"); the pool
graph exists by totality. `MemoSelectedReports` then lifts the unguarded report to the guarded
program.

**(b) Occurrence of the seed in the cover pool — blocked by opaque witnesses.**
What (a) does not give is `memberGraph pool seed` for the two seeds of K1 and K2 (the packed
variable payload `consTerm 0 (consTerm dom (consTerm name 0))` and the application seed
`auxiliaryTerm dom cod fn arg`). The pool is the output of the cover
`C = measuredStrictCover V tv baseM = selectedCover (unitAuxSyntax V tv) (chosenMeasure baseM)`
(`NumberedWindowInternalLiteralStrictMeasuredScratchProof.lean:41`) on the seed. `V` (term syntax)
and `baseM` (term measure) are existential witnesses:

- chosen in `NumberedWindowInternalFactoredCoverNumericProof.selected`
  (`obtain ⟨V,_⟩ := termProgram`, `obtain ⟨M,_⟩ := measureExists`, `obtain ⟨G,_⟩ := grammarExists`),
  exported as `exact_SelectedFactoredCover` (`NumberedWindowInternalFactoredCoverChecks.lean:31`);
- consumed in `exact_ConcreteLambdaJoinedMemoPacketAt`
  (`NumberedWindowInternalLiteralLambdaJoinedMemoPacketProof.lean`,
  `obtain ⟨V,baseM,_,vFit,mFit,_,_⟩ := exact_SelectedFactoredCover`), from where they reach the
  window of `exact_InstalledLambdaWindowWithScalarAtOriginalWindow`.

Their only properties are numerical calibrations (`TermSyntaxCalibrated`, `TermMeasureCalibrated`,
`ActualSelectedCoverOutput`). No open-term law says that the cover of a seed lists the seed, and
none can be derived from a calibration: this is the round-6 situation exactly (opaque `∃ p`
witness, open input). So the failure is **opacity, not control flow**. I did not open
`termProgram`, `measureExists`, `grammarExists` or `selectedCover`; if one of them is already
explicit code, the missing fact for it is the closure law stated below.

K1 has a second opaque dependency: the scalar of the fresh address needs
`windowAt (joinedAuxiliaryWindow s base Tg V tv baseM) ctx dom payload`
(`exact_OpenLiteralScalarFromSelfLeast`), and `base`, `T` come from `exact_WindowPrimitiveLeaves s`
in the same packet proof.

## What a visible-code variant would have to provide

Either of the following makes (b) derivable; both need explicit syntax code.

1. Explicit cover. A syntax checker `V` and generator written as visible recursions, with the
   internal law "if `V` accepts the seed, the generated pool at the seed's measure lists the seed",
   and two closure laws of `V` on open terms: it accepts the variable payload built from a listed
   domain code and a name, and it accepts `auxiliaryTerm dom cod fn arg` when it accepts `fn` and
   `arg` at matching types. (`V` accepting `fn` is derivable from the carrier of `q`: its self-least
   report puts `fn` in its own pool, and the cover's outer `branch (rawCall V) 0 …` returns zero
   unless `V` accepts.)
2. Guarded cover. A cover that prepends the seed when `V` accepts it makes the occurrence
   shape-determined, but still needs the same two closure laws of `V`. Prepending without the test
   is not available: it changes the all-input calibration (the zero round is written "without
   inserting it into a pool where it does not occur").

The window half of K1 needs the same for `base`/`T` (`strictAuxWindow`), or a guard of the same kind.

## A second, structural gap

`exact_InstalledLambdaWindowWithScalarAtOriginalWindow` does not export the code of `A.least`
(in its proof `L := memoFilteredLeast C memo s`, an equation by `rfl`) nor the least laws
(`MemoSelectedReports`, obtained inside the packet from `exact_OpenTypedMemoLeastLaws` and dropped
before the joined rules). Instantiating (a) at K1/K2 on `literalProbeWindow A` needs a selection
theorem that also returns `A.least = memoFilteredLeast C Base s` and `MemoSelectedReports C s Base`
for the same `C`, `Base`. That is a restatement of existing proofs, not new arithmetic.

## Status of K1 and K2

`FreshAddressCarrier` and `FreshSeedLeast` are not proved for any window. They are reduced to:
(a) `SeedMemberLeast` (derivable, not written), (b) pool occurrence of two seeds (blocked on `V`,
the measure and the generator), the window test at the variable payload (blocked on `base`, `T`),
and the export of the least program's code.
