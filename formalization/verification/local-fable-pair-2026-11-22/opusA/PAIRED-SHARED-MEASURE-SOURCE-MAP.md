# Paired shared measure — source map (Opus A, 2026-11-22)

**Target** `LogicLineages/PersistentMarking/NumberedWindowInternalCoverCombinedRestrictedPairedSharedMeasureTargets.lean`.

**Serves.** Paper 16 frontier, combined restricted paired route. #1379/#1386 and task 1
(`…PairedCommonLeast`) all retain the hypothesis that the two *applications*
`a := auxiliaryTerm dom cod f arg`, `b := auxiliaryTerm dom cod g arg` have one shared selected measure
`m` (`unary (selectedMeasure P.R) m a`, `… m b`); the handoff calls it "the actual shared parent measure
assumption". This target replaces it by the function-level statement that `f` and `g` have one shared
selected measure, under the same selected program.

**Statements.**
1. `ExactOpenSharedAuxMeasureEquality` — generic in `M`: `unary (sharedMeasure M) m fn`,
   `… m fn'`, `… x (auxiliaryTerm dom cod fn arg)`, `… y (auxiliaryTerm dom cod fn' arg)` give `eqn x y`.
   This is #858's equality, restated for `sharedMeasure M = selectedMeasure (sharedMeasureUpdate M)`,
   which is what the combined programs use (`P.R` unfolds to `sharedMeasureUpdate (fittedMeasureBase …)`).
   #858 itself is for `selectedMeasure (measureUpdate base combine)` and does not apply literally.
2. `…PairedSharedMeasureParent` — at the chosen `P`: shared function measure ⇒ a fresh common
   application measure `p` (continuation). Application-measure existence comes from `programCases`.
3. `…PairedSharedMeasureEdge` — #1386's `…PairedEdge` with hypotheses 6–7 replaced by the function measure.
4. `…PairedSharedMeasureCommonLeast` — task 1's common least with hypotheses 6–7 replaced likewise.

**Assumed.** Exactly the #1386 parent hypotheses except that the shared application measure is
replaced by `unary (selectedMeasure P.R) m f` and `unary (selectedMeasure P.R) m g`.

**Suppliers (accepted).** #1076 `exact_OpenCoverSharedAuxMeasureParent` (decomposition of a tag-six
parent measure into function/argument selected measures and `chosenCombine p ![mf,ma]`); `valueUnique`,
`programCases`, `outputTransport`, `graphInputTransport`; #1386 `…PairedEdge`; task 1 `…PairedCommonLeast`.

**Not claimed.** That the shared function measure follows from the parent edges: it does not in general
(`directedX base P.V` is built over an arbitrary `base : Program 2`; nothing in the edge or the windows
compares the measures of `f` and `g`). Nor that the function-level hypothesis is implied by the old
application-level one (that would need `chosenCombine` injective in its first argument, which no accepted
lemma provides). Nothing about reached pools, lengths, or different raw representatives.
