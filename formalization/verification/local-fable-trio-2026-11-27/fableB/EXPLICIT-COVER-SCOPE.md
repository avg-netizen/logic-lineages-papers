# Scope of the opacity repair for K1/K2 (continuation item C)

Fable B, 27 November 2026. Reading only; no proofs. File names are under
`LogicLineages/PersistentMarking/`. "Verified" means I read the cited lines this round;
"not opened" means I did not.

## Correction to `SEED-MEMBER-REPORT.md`

That report named the cover's generator among the opaque witnesses. That is wrong for the
installed cover. The installed cover is

`measuredStrictCover V tv baseM = selectedCover (unitAuxSyntax V tv) (chosenMeasure baseM)`
(`NumberedWindowInternalLiteralStrictMeasuredScratchProof.lean:41`), and
`selectedCover V M = factoredCover V M selectedGrammarOption`
(`NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets.lean:27`), with
`factoredCover V M G = branch (rawCall V) 0 (generatorCall M G)`
(`NumberedWindowInternalFactoredCoverTargets.lean:40`).
The generator is the **named program** `selectedGrammarOption = succ ∘ termListAtMeasure`
(`NumberedWindowInternalCoverSelectedGrammarOptionTargets.lean:16–21`), not the `grammarExists`
witness: `exact_ConcreteLambdaJoinedMemoPacketAt` discards that component
(`obtain ⟨V,baseM,_,vFit,mFit,_,_⟩ := exact_SelectedFactoredCover`). The syntax and measure
arguments are also visible wrappers around the witnesses, not the witnesses themselves:
`chosenMeasure base = selectedMeasure (measureUpdate base chosenCombine)`
(`…CoverSelectedGrammarAuxScratchMeasuredTargets.lean:27`) and `unitAuxSyntax V TV`
(a memo of the same `selectedMeasure` kind; `auxSyntax V T = selectedMeasure (auxSyntaxUpdate V T)`
in `NumberedWindowInternalCoverAuxSyntaxTargets.lean:38`). So opacity sits only at the **leaf
programs** those wrappers call.

## Witness list

| Witness | Where chosen (verified) | Kind | Function it realizes |
| --- | --- | --- | --- |
| `V` (raw term syntax leaf) | `NumberedWindowSyntaxProgramProof.termProgram := program (Primrec.fst.comp bits)`, where `program` is `(GorbowPRProgram.Proof.unaryCorrespondence _).mp …`; taken in `NumberedWindowInternalFactoredCoverNumericProof.selected` line 90 | Primrec realization, non-constructive | `fun n => (bits n).1` (raw term syntax bit) |
| `baseM` (base term measure) | `…FactoredCoverNumericProof.measureExists` (line 55), `unaryCorrespondence` of `Primrec.encode.comp (Primrec.fst.comp metrics)` | Primrec realization | `fun n => encode (bounds n).1` (node count and maximum numeral) |
| grammar `G` | `…FactoredCoverNumericProof.grammarExists` (line 58), Primrec realization of `grammar H K m.2 m.1` | Primrec realization — **not used** by the installed cover | — (replaced by `selectedGrammarOption`) |
| `base` (window leaf) | `NumberedWindowInternalAuxWindowStepPrograms.exact_WindowPrimitiveLeaves` line 55: `Proof.allPrimitiveFunctions 2 _ (intrinsicPrimitive s W window)`, with `W` from `packedWindowWitness s` | Primrec realization (twice: `W` is itself `∃ wp, ActualPackedWindow s wp` by `Primrec.cond …`) | the intrinsic window step on `(ctx, raw)` |
| `T` (type-guard leaf) | same theorem, line 60: `unaryCorrespondence` of `fun n => (typeGuard s n).toNat` | Primrec realization | type-guard bit |
| `X` / `baseX` (exchange) | `exact_SelectedPackedScalarEdge s` in the packet proof | not opened | term exchange (`ActualTermExchange`) |

None of these is "an explicit term hidden behind an `∃`": in every opened case the program comes
from the Primrec-realization theorem of `GorbowPRProgram.Proof`. Exporting a term is therefore
not available; for each leaf either an explicit program must be written, or the open-term law
must be obtained another way (below).

## What each seed needs, given the visible wrappers

**Application seed `auxiliaryTerm dom cod fn arg` (K2).** It is an auxiliary node (tag 6), which the
wrappers treat by visible recursion on the children. Existing open laws in that direction, found
but not checked line by line: `exact_OpenUnitAuxSyntaxOperands` (operands valid from the node
valid — elimination), `exact_OpenJoinedAuxiliaryParent` (used in
`NumberedWindowInternalLiteralBiAuxWindowLiftProof.lean`; a parent-from-children window law),
`ExactAuxMeasureRecurrence` (`NumberedWindowInternalAuxMeasureMemoTargets.lean:47`), and the
`…CoverSelectedGrammarOpen{Base,Row,Step}Proof` / `…AuxScratchMembershipProof` family for the
generator. The missing statements are the **introduction** direction at an auxiliary node:
(i) `unitAuxSyntax V tv` accepts `auxiliaryTerm dom cod fn arg` when it accepts `fn` and `arg` and
the type guards hold; (ii) the generated list at the node's measure lists the node when it lists
the children at theirs. Both are about visible code (the memo recursion and `selectedTerms`) and
call the opaque leaves only on `fn` and `arg`, where the needed facts are *premises* (they follow
from the carriers of `q` and `u`: each stored coordinate has a self-least report, hence occurs in
its own pool by `exact_OpenPackedLeastPoolOccurrence`, hence passed the cover's `rawCall V`
branch). So **K2 does not need an explicit leaf program**. It needs (a) `SeedMemberLeast`,
(b) the two introduction laws (i)/(ii) for the visible wrappers, and (c) the window half, where
`SelectedSeedFormation` (`NumberedWindowInternalLiteralApplicationFormationSeamProof.lean`) is the
existing statement and `exact_OpenJoinedAuxiliaryParent` the likely supplier.

**Variable payload `consTerm 0 (consTerm dom (consTerm name 0))` (K1).** This is a leaf of the raw
syntax. Acceptance by the syntax program and the measure at an open leaf are facts about `V` and
`baseM` themselves, unless `unitAuxSyntax`/`chosenMeasure` decide variable nodes before calling the
leaf (not opened; the name "unit" and the existing `freeSource` atom test suggest checking this
first). If they do not, **K1 needs explicit code for the variable case**: either an explicit `V`
and `baseM` (full raw-term syntax bit and measure: two structural recursions over the packed term
code, of the size of `selectedTerms` each, with their numeric calibrations and the restatement of
every theorem that takes `TermSyntaxCalibrated V` / `TermMeasureCalibrated M` as a hypothesis —
those are stated for arbitrary calibrated programs, so they re-instantiate without edits), or a
visible front test "is a variable node of a listed type" placed before the leaf call in the
wrappers, calibrated against the leaf on all inputs. The window half of K1
(`windowAt (joinedAuxiliaryWindow …) ctx dom payload`) has the same shape for `base`/`T`.

## The guarded-cover route

Confirmed: a cover that prepends the seed when the syntax test accepts does not avoid the
syntax facts. It makes "seed listed in its pool" shape-determined, but the guard itself is
`V`-acceptance of the open seed. For the application seed that acceptance is law (i) above
(visible, derivable); for the variable payload it is the leaf fact. So the guard would replace
law (ii) (generator lists the node) and nothing else; it does not remove the need for an explicit
treatment of the variable leaf.

## Summary list

| Open-term law | Needed for | Status |
| --- | --- | --- |
| `SeedMemberLeast` | K1, K2 | visible code, inductive; frozen, not proved |
| context option successor at an admitted context | K1, K2 | derivable from the address's self-least report |
| aux-node syntax introduction (i) | K2 | visible wrapper; not written |
| aux-node listed in generated pool (ii) | K2 | visible generator `selectedGrammarOption`; not written |
| window at the application seed | K2 | `SelectedSeedFormation`; supplier `exact_OpenJoinedAuxiliaryParent` (not checked) |
| syntax / measure / window at the variable payload | K1 | leaf facts about `V`, `baseM`, `base`, `T` (Primrec realizations) unless the wrappers decide variable nodes first — to be checked before writing any program |
| least code and report law of the window | K1, K2 | **done**: `exact_LiteralWindowWithLeast` |
