module
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedParentHopsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOpenMatchedBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnCoverageProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnMembersProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedMatchedCallsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm functionWitnessTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (graph5Rename)
open NumberedWindowInternalSparsePathAdvanceTargets (actualCalls)
open NumberedWindowInternalSparsePositiveTransitivityTargets (supplied)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralEnrichedEdgeReversalProof (CanReverse)
open NumberedWindowInternalLiteralRoundObserverTargets (Preserves)
open NumberedWindowInternalLiteralPackedLeastOnProof (packedLeastOn leastOnGraph)
open NumberedWindowInternalLiteralLeastOnFixedPointProof (WindowEndpoints casesLeastOn)
open NumberedWindowInternalLiteralLeastOnCoverageProof (exact_OpenLeastOnFromCoverage)
open NumberedWindowInternalLiteralLeastOnMembersProof (leastOnRename)
open NumberedWindowInternalLiteralTypeMembershipTargets (literalMembership)
open NumberedWindowInternalLiteralTypedMemoUnfoldingProof (recursiveTypedMemo)
open NumberedWindowInternalLiteralTypedMemoLeastLawsProof (memoFilteredLeast MemoSelectedReports)
open NumberedWindowInternalLiteralStrictMeasuredScratchProof (measuredStrictCover)
open NumberedWindowInternalLiteralStrictMeasuredMemoTransportProof (selectedBiAuxType exact_OpenBiAuxTypeEvidence)
open NumberedWindowInternalLiteralBiAuxBaseWindowLiftProof (joinedBiAuxBase)
open NumberedWindowInternalLiteralJoinedAuxiliaryWindowProof (joinedAuxiliaryWindow)
open NumberedWindowInternalLiteralJoinedRawFunctionLiftProof (selectedJoinedRaw)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (finiteScalar)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralOpenMatchedReportProof
open NumberedWindowInternalLiteralOpenMatchedBindingProof (provideEarlier pulledRename moveTarget)
open NumberedWindowInternalLiteralJoinedPathHopProof
open NumberedWindowInternalLiteralJoinedParentHopsProof
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)

attribute [local irreducible] programGraph recursiveTypedMemo packedLeastOn rawWithTarget
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
private theorem functionWitnessRename {β : Type} (w : OTerm α) (j : α → β) :
    (functionWitnessTerm w).relabel j = functionWitnessTerm (w.relabel j) := by
  simp only [functionWitnessTerm,rawConsRename,numeralRename,zRelabel]

/-- At already selected raw parent minima, match the same two
representatives as the child's certified calls. The later application
value is the actual existing later report, by graph functionality. -/
theorem exact_OpenJoinedMatchedSelected (s : Settings) (X base : Program 2) (T V baseM cv tv : Program 1)
    (leaf : Nat → Program 3) (other : Program 3) (finite : List Nat)
    (ctx dom cod arg f g q w r value a b : OTerm α) :
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
    let qa := auxiliaryTerm dom cod q arg
    let ra := auxiliaryTerm dom cod r arg
    CanReverse Base → WindowEndpoints W E → Preserves E L₀ → MemoSelectedReports C s Base →
    D B Γ (typedFormation K ctx dom cod arg) →
    D B Γ (reported L ctx (rawCons dom cod) q f) →
    D B Γ (reported L ctx (rawCons dom cod) r g) →
    D B Γ (reported L ctx cod (auxiliaryTerm dom cod g arg) value) →
    D B Γ (windowAt W ctx cod ra) →
    D B Γ (programGraph raw (suc z) ![ctx,cod,qa,functionWitnessTerm w,ra]) →
    D B Γ (leastOnGraph C E s ctx cod qa a) → D B Γ (leastOnGraph C E s ctx cod ra b) →
    D B Γ (pulled L R ctx cod (auxiliaryTerm dom cod f arg) value) := by
  intro Tg C W Base E L₀ L i raw R K qa ra reverse ends stable selected held fMin gMin last target arc left right
  obtain ⟨typed⟩ := held
  let both := Derivation.conjunctionLeft typed
  let guards := Derivation.conjunctionRight typed
  let scope := Derivation.conjunctionRight guards
  have types := exact_OpenBiAuxTypeEvidence s T tv dom cod
    ⟨Derivation.conjunctionLeft both⟩ ⟨Derivation.conjunctionRight both⟩
  have fixed : D B Γ (windowAt W ctx dom arg) := ⟨Derivation.conjunctionLeft guards⟩
  have src := exact_OpenJoinedFunctionRepresentative s X base Tg V tv baseM ctx dom cod arg q f a
    reverse stable types fixed fMin left
  have dst := exact_OpenJoinedFunctionRepresentative s X base Tg V tv baseM ctx dom cod arg r g b
    reverse stable types fixed gMin right
  have found := selected B α Γ ctx cod (auxiliaryTerm dom cod f arg) a src
  have there := selected B α Γ ctx cod (auxiliaryTerm dom cod g arg) b dst
  obtain ⟨eq⟩ := valueUnique L (suc b) (suc value) (![ctx,cod,auxiliaryTerm dom cod g arg] : Fin 3 → OTerm α) there last
  have path := exact_OpenJoinedPositiveAtParents s X base Tg V tv baseM cv tv leaf other finite
    ctx cod qa (functionWitnessTerm w) ra a b ends stable selected ⟨Derivation.conjunctionLeft scope⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight scope)⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight scope)⟩ target arc left right
  obtain ⟨found⟩ := found
  obtain ⟨path⟩ := path
  obtain ⟨same⟩ := moveTarget R L ctx cod a b value (cancelSuc eq) path
  exact provideEarlier L R ctx cod (auxiliaryTerm dom cod f arg) value a found same

/-- Discharge the abstract local matching law using the full, installed
recursive least, the original positive wrapper, and the two physical
window reports. Both existential choices are real least reports. -/
theorem exact_OpenJoinedMatchedCalls (s : Settings) (X base : Program 2) (T V baseM cv tv : Program 1)
    (leaf : Nat → Program 3) (other : Program 3) (finite : List Nat) :
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
    MatchedCallsAt K L R := by
  intro Tg C W Base E L₀ L i raw R K reverse ends stable selected B α Γ ctx dom cod arg f g q w r value least H
  let Δ := H :: Γ
  have h : Derivation B Δ H := Derivation.hypothesis List.mem_cons_self
  let fa := auxiliaryTerm dom cod f arg
  let ga := auxiliaryTerm dom cod g arg
  let qa := auxiliaryTerm dom cod q arg
  let ra := auxiliaryTerm dom cod r arg
  let goal := pulled L R ctx cod fa value
  have form : D B Δ (typedFormation K ctx dom cod arg) := ⟨Derivation.conjunctionLeft h⟩
  let facts := Derivation.conjunctionLeft (Derivation.conjunctionRight h)
  have left : D B Δ (reported L ctx (rawCons dom cod) q f) := ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight facts)⟩
  have right : D B Δ (reported L ctx (rawCons dom cod) r g) := ⟨Derivation.conjunctionRight (Derivation.conjunctionRight facts)⟩
  have last : D B Δ (reported L ctx cod ga value) := ⟨Derivation.conjunctionRight (Derivation.conjunctionRight h)⟩
  obtain ⟨formD⟩ := form
  let both := Derivation.conjunctionLeft formD
  have types := exact_OpenBiAuxTypeEvidence s T tv dom cod
    ⟨Derivation.conjunctionLeft both⟩ ⟨Derivation.conjunctionRight both⟩
  obtain ⟨qW,rW,arc⟩ := exact_OpenJoinedParentHops s base Tg V tv baseM i cv tv L leaf other ctx dom cod q w r arg
    types ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight formD)⟩ ⟨Derivation.conjunctionLeft facts⟩
  have qCovered := exact_OpenJoinedWindowCoverage s base Tg V tv baseM ctx cod qa qW
  have rCovered := exact_OpenJoinedWindowCoverage s base Tg V tv baseM ctx cod ra rW
  have qHas := exact_OpenLeastOnFromCoverage C E s ctx cod qa qCovered
  have rHas := exact_OpenLeastOnFromCoverage C E s ctx cod ra rCovered
  have out : D B Δ goal := by
    apply casesLeastOn C E s ctx cod qa goal qHas
    intro β j Θ a keep aLeast
    have rHas' := renameInto rHas j Θ keep
    rw [NumberedWindowInternalLiteralLeastOnMembersProof.hasOnRename] at rHas'
    apply casesLeastOn C E s (ctx.relabel j) (cod.relabel j) (ra.relabel j) (goal.relabel j) rHas'
    intro γ k I b hold bLeast
    let n := k ∘ j
    have nKeep (p : Formula α) (hp : p ∈ Δ) : p.relabel n ∈ I := by
      simpa only [n,ID1Completion.InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using hold _ (keep p hp)
    rw [ID1Completion.InternalPositiveUnfoldingSupportProof.formulaRelabelComposition]
    change D B I ((pulled L R ctx cod fa value).relabel n)
    rw [pulledRename,show fa.relabel n = auxiliaryTerm (dom.relabel n) (cod.relabel n) (f.relabel n) (arg.relabel n) from auxiliaryRename _ _ _ _ _]
    have form' := renameInto ⟨formD⟩ n I nKeep
    rw [typedFormationRename] at form'
    have left' := renameInto left n I nKeep
    rw [reportedRename,rawConsRename] at left'
    have right' := renameInto right n I nKeep
    rw [reportedRename,rawConsRename] at right'
    have val := renameInto last n I nKeep
    simp only [reportedRename,ga,auxiliaryRename] at val
    have target := renameInto rW n I nKeep
    simp only [windowRename,auxiliaryRename] at target
    have hit := renameInto arc n I nKeep
    simp only [graph5Rename,sucRelabel,zRelabel,auxiliaryRename,functionWitnessRename] at hit
    have source := renameInto aLeast k I hold
    simp only [leastOnRename,qa,auxiliaryRename,Term.relabel_relabel] at source
    simp only [n,ra,auxiliaryRename,Term.relabel_relabel] at bLeast ⊢ form' left' right' val target hit
    exact exact_OpenJoinedMatchedSelected s X base T V baseM cv tv leaf other finite
      (ctx.relabel n) (dom.relabel n) (cod.relabel n) (arg.relabel n) (f.relabel n) (g.relabel n)
      (q.relabel n) (w.relabel n) (r.relabel n) (value.relabel n) (a.relabel k) b reverse ends stable selected
      form' left' right' val target hit source bLeast
  obtain ⟨out⟩ := out
  exact ⟨Derivation.implicationIntroduction out⟩

#print axioms exact_OpenJoinedMatchedSelected
#print axioms exact_OpenJoinedMatchedCalls
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedMatchedCallsProof
