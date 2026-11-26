module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedMatchedCallsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOpenMatchedForwardBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOpenMatchedPathProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOpenMatchedAdvanceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOpenMatchedCompositionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnCoverageProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalThinMatchedForwardBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedForwardPathProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (positiveAt)
open NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof (positiveRename)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralEnrichedEdgeReversalProof (CanReverse)
open NumberedWindowInternalLiteralRoundObserverTargets (Preserves)
open NumberedWindowInternalLiteralPackedLeastOnProof (packedLeastOn leastOnGraph)
open NumberedWindowInternalLiteralLeastOnFixedPointProof (WindowEndpoints casesLeastOn)
open NumberedWindowInternalLiteralLeastOnCoverageProof (exact_OpenLeastOnFromCoverage)
open NumberedWindowInternalLiteralTypedMemoUnfoldingProof (recursiveTypedMemo)
open NumberedWindowInternalLiteralTypedMemoLeastLawsProof (memoFilteredLeast MemoSelectedReports)
open NumberedWindowInternalLiteralStrictMeasuredScratchProof (measuredStrictCover)
open NumberedWindowInternalLiteralStrictMeasuredMemoTransportProof (selectedBiAuxType exact_OpenBiAuxTypeEvidence)
open NumberedWindowInternalLiteralBiAuxBaseWindowLiftProof (joinedBiAuxBase)
open NumberedWindowInternalLiteralJoinedAuxiliaryWindowProof (joinedAuxiliaryWindow exact_OpenJoinedAuxiliaryParent)
open NumberedWindowInternalLiteralJoinedRawFunctionLiftProof (selectedJoinedRaw)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (finiteScalar)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralOpenMatchedReportProof
open NumberedWindowInternalLiteralOpenMatchedCompositionProof (pullCases)
open NumberedWindowInternalLiteralOpenMatchedForwardBindingProof (pushed pushedRename provideLater)
open NumberedWindowInternalLiteralOpenMatchedAdvanceProof (exact_MatchedAdvance)
open NumberedWindowInternalLiteralOpenMatchedPathProof (exact_MatchedPath)
open NumberedWindowInternalLiteralJoinedMatchedCallsProof (exact_OpenJoinedMatchedCalls)
open NumberedWindowInternalLiteralJoinedParentHopsProof (exact_OpenJoinedWindowCoverage)
open NumberedWindowInternalThinMatchedForwardBindingProof (moveSource)

attribute [local irreducible] programGraph recursiveTypedMemo packedLeastOn rawWithTarget
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- A positive function certificate of arbitrary length is mapped to an
actual positive application certificate. It starts at the same old
application output, by functionality of the installed full least. -/
theorem exact_OpenJoinedForwardPath (s : Settings) (X base : Program 2) (T V baseM cv tv : Program 1)
    (leaf : Nat → Program 3) (other : Program 3) (finite : List Nat)
    (ctx dom cod arg f g cert value : OTerm α) :
    let Tg := selectedBiAuxType s T tv
    let C := measuredStrictCover V tv baseM
    let W := joinedAuxiliaryWindow s base Tg V tv baseM
    let Base := joinedBiAuxBase s X base Tg V tv baseM
    let E := recursiveTypedMemo Base
    let L₀ := packedLeastOn C E s
    let L := memoFilteredLeast C Base s
    let i := finiteScalar (addressScalar cv tv W L) finite
    let raw := selectedJoinedRaw s base Tg V tv baseM leaf other
    let R := rawWithTarget i cv tv raw L
    let K : MatchContext := ⟨Tg,cv,tv,finite,W⟩
    CanReverse Base → WindowEndpoints W E → Preserves E L₀ → MemoSelectedReports C s Base →
    D B Γ (typedFormation K ctx dom cod arg) →
    D B Γ (windowAt W ctx (rawCons dom cod) g) →
    D B Γ (positiveAt R L ctx (rawCons dom cod) f cert g) →
    D B Γ (reported L ctx cod (auxiliaryTerm dom cod f arg) value) →
    D B Γ (windowAt W ctx cod (auxiliaryTerm dom cod g arg)) ∧ D B Γ (pushed L R ctx cod (auxiliaryTerm dom cod g arg) value) := by
  intro Tg C W Base E L₀ L i raw R K reverse ends stable selected form fn path earlier
  let parent := auxiliaryTerm dom cod g arg
  obtain ⟨guards⟩ := form
  let two := Derivation.conjunctionLeft guards
  have types := exact_OpenBiAuxTypeEvidence s T tv dom cod ⟨Derivation.conjunctionLeft two⟩ ⟨Derivation.conjunctionRight two⟩
  have formed := (exact_OpenJoinedAuxiliaryParent s base Tg V tv baseM ctx dom cod g arg types fn
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight guards)⟩).1
  have cov := exact_OpenJoinedWindowCoverage s base Tg V tv baseM ctx cod parent formed
  have found := exact_OpenLeastOnFromCoverage C E s ctx cod parent cov
  have out : D B Γ (pushed L R ctx cod parent value) := by
    apply casesLeastOn C E s ctx cod parent _ found
    intro β j Δ later keep min
    rw [pushedRename]
    simp only [parent,auxiliaryRename] at min ⊢
    let c := ctx.relabel j
    let d := dom.relabel j
    let k := cod.relabel j
    let a := arg.relabel j
    let p := f.relabel j
    let q := g.relabel j
    have after : D B Δ (reported L c k (auxiliaryTerm d k q a) later) := selected B β Δ c k (auxiliaryTerm d k q a) later min
    have h := renameInto ⟨guards⟩ j Δ keep
    rw [typedFormationRename] at h
    have step := renameInto path j Δ keep
    rw [positiveRename,rawConsRename] at step
    have before := renameInto earlier j Δ keep
    rw [reportedRename,auxiliaryRename] at before
    have matched := exact_OpenJoinedMatchedCalls s X base T V baseM cv tv leaf other finite reverse ends stable selected
    obtain ⟨rule⟩ := exact_MatchedPath K L R (exact_MatchedAdvance K L R matched) B β Δ c d k a p q (cert.relabel j) later
    obtain ⟨h⟩ := h
    obtain ⟨step⟩ := step
    obtain ⟨after⟩ := after
    have mapped := Derivation.implicationElimination rule (Derivation.conjunctionIntroduction h (Derivation.conjunctionIntroduction step after))
    apply pullCases L R c k (auxiliaryTerm d k p a) later _ ⟨mapped⟩
    intro γ n Θ old stay got trail
    rw [pushedRename,auxiliaryRename]
    rw [auxiliaryRename] at got
    have initial := renameInto before n Θ stay
    rw [reportedRename,auxiliaryRename] at initial
    have final := renameInto (⟨after⟩ : D B Δ (reported L c k (auxiliaryTerm d k q a) later)) n Θ stay
    rw [reportedRename,auxiliaryRename] at final
    obtain ⟨same⟩ := valueUnique L (suc old) (suc ((value.relabel j).relabel n))
      ![c.relabel n,k.relabel n,auxiliaryTerm (d.relabel n) (k.relabel n) (p.relabel n) (a.relabel n)] ⟨got⟩ initial
    obtain ⟨path'⟩ := moveSource R L (c.relabel n) (k.relabel n) old ((value.relabel j).relabel n)
      (later.relabel n) (cancelSuc same) trail
    obtain ⟨final⟩ := final
    exact provideLater L R (c.relabel n) (k.relabel n) (auxiliaryTerm (d.relabel n) (k.relabel n) (q.relabel n) (a.relabel n))
      ((value.relabel j).relabel n) (later.relabel n) final path'
  exact ⟨formed,out⟩

#print axioms exact_OpenJoinedForwardPath
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedForwardPathProof
