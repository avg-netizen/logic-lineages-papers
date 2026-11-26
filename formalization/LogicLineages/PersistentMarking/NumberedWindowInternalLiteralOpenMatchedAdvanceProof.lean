module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOpenMatchedAdvanceLawProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOpenMatchedCompositionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOpenMatchedBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalThinFormationRepresentativeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceWitnessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOpenMatchedAdvanceProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination addHyp)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalLiteralOpenMatchedReportProof
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparsePathSuccessfulAdvanceChecks (exact_OpenSuccessfulAdvanceCalls)
open NumberedWindowInternalSparsePathSuccessfulAdvanceWitnessProof (reportCases)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph)
open NumberedWindowInternalSparsePathAdvanceOpenSyntaxProof (quadRename)
open NumberedWindowInternalLiteralOpenMatchedReportProof (pulled MatchedCallsAt)
open NumberedWindowInternalLiteralOpenMatchedBindingProof (pulledRename)
open NumberedWindowInternalLiteralOpenMatchedCompositionProof (pullCases continuePath)
open NumberedWindowInternalLiteralOpenMatchedAdvanceLawProof
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
variable (K : MatchContext) (L : Program 3) (raw : Program 5)
attribute [local irreducible] ID1Completion.InternalControlGraph.programGraph


private theorem one (law : MatchedCallsAt K L raw) (ctx dom cod arg fn next hop value : OTerm α)
    (domain : Derivation body Γ (typedFormation K ctx dom cod arg))
    (step : Derivation body Γ (selectedGraph raw (L)
      (suc next) ctx (rawCons dom cod) (suc fn) hop))
    (found : Derivation body Γ (reported L ctx cod (auxiliaryTerm dom cod next arg) value)) :
    Nonempty (Derivation body Γ (pulled L raw ctx cod (auxiliaryTerm dom cod fn arg) value)) := by
  let least := L
  obtain ⟨succeeded⟩ := exact_OpenSuccessfulAdvanceCalls body raw least α ctx (rawCons dom cod) fn hop next
  have facts := Derivation.implicationElimination (Derivation.conjunctionLeft (weakenClosed succeeded Γ)) step
  apply reportCases raw least ctx (rawCons dom cod) fn hop next _ ⟨facts⟩
  intro β j Δ q child r keep pair
  rw [pulledRename,auxiliaryRename]
  have d := renameInto ⟨domain⟩ j Δ keep
  rw [typedFormationRename] at d
  have v := renameInto ⟨found⟩ j Δ keep
  rw [reportedRename,auxiliaryRename] at v
  rw [rawConsRename] at pair
  obtain ⟨p⟩ := pair
  obtain ⟨d⟩ := d
  obtain ⟨v⟩ := v
  obtain ⟨rule⟩ := law body β Δ _ _ _ _ (fn.relabel j) (next.relabel j) q child r (value.relabel j)
  exact ⟨Derivation.implicationElimination rule
    (Derivation.conjunctionIntroduction d (Derivation.conjunctionIntroduction (Derivation.conjunctionRight p) v))⟩

theorem exact_MatchedAdvance : ExactMatchedAdvance := by
  intro K L raw law body α Γ ctx dom cod arg fn next hop value least step later
  let H := typedFormation K ctx dom cod arg ⊓ (step ⊓ later)
  let Δ := H :: Γ
  let a := auxiliaryTerm dom cod fn arg
  let b := auxiliaryTerm dom cod next arg
  let target := pulled L raw ctx cod a value
  let found := reported L ctx cod b value
  let suffix := pulled L raw ctx cod b value
  have h : Derivation body Δ H := Derivation.hypothesis List.mem_cons_self
  have typing := Derivation.conjunctionLeft h
  have accepted := Derivation.conjunctionLeft (Derivation.conjunctionRight h)
  have tailCase := Derivation.conjunctionRight (Derivation.conjunctionRight h)
  have direct : Derivation body (found :: Δ) found := Derivation.hypothesis List.mem_cons_self
  obtain ⟨directPath⟩ := one K L raw law ctx dom cod arg fn next hop value
    (addHyp typing found) (addHyp accepted found) direct
  have chain : Nonempty (Derivation body (suffix :: Δ) target) := by
    apply pullCases L raw ctx cod b value target ⟨Derivation.hypothesis List.mem_cons_self⟩
    intro β j Θ mid keep getMid rest
    change Nonempty (Derivation body Θ ((pulled L raw ctx cod a value).relabel j))
    rw [pulledRename]
    have form := renameInto ⟨addHyp typing suffix⟩ j Θ keep
    rw [typedFormationRename] at form
    have before := renameInto ⟨addHyp accepted suffix⟩ j Θ keep
    simp only [step,selectedGraph,quadRename,sucRelabel,rawConsRename] at before
    simp only [a,b,auxiliaryRename] at getMid ⊢
    obtain ⟨form⟩ := form
    obtain ⟨before⟩ := before
    have first := one K L raw law _ _ _ _ (fn.relabel j) (next.relabel j) (hop.relabel j) mid form before getMid
    exact continuePath L raw _ _ _ mid (value.relabel j) first ⟨rest⟩
  obtain ⟨chain⟩ := chain
  exact ⟨Derivation.implicationIntroduction (disjunctionElimination tailCase
    (Derivation.implicationIntroduction directPath) (Derivation.implicationIntroduction chain))⟩
#print axioms exact_MatchedAdvance
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOpenMatchedAdvanceProof
