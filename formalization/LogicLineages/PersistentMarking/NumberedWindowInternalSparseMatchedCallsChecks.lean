module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMatchedCallsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMatchedCallsBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFormationRepresentativeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationHopChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityFormulaProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseMatchedCallsChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm functionWitnessTerm)
open NumberedWindowInternalSparseStructuralApplicationTargets (window)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePathAdvanceTargets (actualCalls)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseFormationRepresentativeTargets (formation)
open NumberedWindowInternalSparseFormationRepresentativeSyntaxProof (atFunction formationRename)
open NumberedWindowInternalSparseApplicationHopTargets (hopData)
open NumberedWindowInternalSparseApplicationHopChecks (exact_ExistentialApplicationHop)
open NumberedWindowInternalSparseMatchedCallsBindingProof (hopCases pulledRename provideEarlier moveTarget)
open NumberedWindowInternalSparseMatchedCallsTargets
attribute [local irreducible] programGraph

theorem exact_MatchedCalls : ExactMatchedCalls := by
  intro C root other baseW X V s W rep body α Γ ctx dom cod arg fn next q child r value least input
  let raw := typedRaw5 root other W V
  let a := auxiliaryTerm dom cod q arg
  let b := auxiliaryTerm dom cod r arg
  let Δ := input :: Γ
  have h : Derivation body Δ input := Derivation.hypothesis List.mem_cons_self
  have typing := Derivation.conjunctionLeft h
  have calls := Derivation.conjunctionLeft (Derivation.conjunctionRight h)
  have original := Derivation.conjunctionLeft calls
  obtain ⟨typed⟩ := NumberedWindowInternalSparseTypedRawChecks.exact_OpenTypedRaw5 body root other W V α Δ
    ctx (rawCons dom cod) q child r
  have ws := Derivation.conjunctionRight (Derivation.implicationElimination (Derivation.conjunctionLeft typed) original)
  obtain ⟨aq⟩ := atFunction W ctx dom cod arg q typing
  obtain ⟨br⟩ := atFunction W ctx dom cod arg r typing
  have parents := Derivation.conjunctionIntroduction
    (Derivation.implicationElimination aq (Derivation.conjunctionLeft ws))
    (Derivation.implicationElimination br (Derivation.conjunctionRight ws))
  obtain ⟨singleton⟩ := exact_ExistentialApplicationHop C root other baseW V X s body α Δ ctx dom cod arg q child r
  have known := Derivation.implicationElimination singleton (Derivation.conjunctionIntroduction original parents)
  have done : Nonempty (Derivation body Δ (pulled C X W s raw ctx cod (auxiliaryTerm dom cod fn arg) value)) := by
    apply hopCases C X W s raw ctx cod a (functionWitnessTerm child) b _ ⟨known⟩
    intro β j Θ left right keep reports
    rw [pulledRename,auxiliaryRename]
    have domain := renameInto ⟨typing⟩ j Θ keep
    rw [formationRename] at domain
    have source : Nonempty (Derivation body Δ (leastGraph C X W s ctx (rawCons dom cod) q fn)) :=
      ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight calls)⟩
    have dest : Nonempty (Derivation body Δ (leastGraph C X W s ctx (rawCons dom cod) r next)) :=
      ⟨Derivation.conjunctionRight (Derivation.conjunctionRight calls)⟩
    have final : Nonempty (Derivation body Δ (leastGraph C X W s ctx cod (auxiliaryTerm dom cod next arg) value)) :=
      ⟨Derivation.conjunctionRight (Derivation.conjunctionRight h)⟩
    have src := renameInto source j Θ keep
    have dst := renameInto dest j Θ keep
    have valueRun := renameInto final j Θ keep
    simp only [leastRename,rawConsRename,auxiliaryRename] at src dst valueRun
    simp only [a,b,auxiliaryRename] at reports
    obtain ⟨reports⟩ := reports
    obtain ⟨src⟩ := src
    obtain ⟨dst⟩ := dst
    obtain ⟨valueRun⟩ := valueRun
    obtain ⟨domain⟩ := domain
    obtain ⟨leftRule⟩ := rep body β Θ _ _ _ _ (q.relabel j) (fn.relabel j) left
    obtain ⟨rightRule⟩ := rep body β Θ _ _ _ _ (r.relabel j) (next.relabel j) right
    have resultL := Derivation.implicationElimination leftRule (Derivation.conjunctionIntroduction domain
      (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft (Derivation.conjunctionLeft reports)) src))
    have resultR := Derivation.implicationElimination rightRule (Derivation.conjunctionIntroduction domain
      (Derivation.conjunctionIntroduction (Derivation.conjunctionRight (Derivation.conjunctionLeft reports)) dst))
    obtain ⟨eq⟩ := valueUnique least (suc right) (suc (value.relabel j)) _ ⟨resultR⟩ ⟨valueRun⟩
    obtain ⟨path⟩ := NumberedWindowInternalSparsePositiveTransitivityFormulaProof.provide raw least
      (ctx.relabel j) (cod.relabel j) left right _ ⟨Derivation.conjunctionRight reports⟩
    obtain ⟨matchPath⟩ := moveTarget raw least _ _ left right (value.relabel j) (cancelSuc eq) path
    exact provideEarlier C X W s raw _ _ _ _ left resultL matchPath
  obtain ⟨done⟩ := done
  exact ⟨Derivation.implicationIntroduction done⟩

#print axioms exact_MatchedCalls
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseMatchedCallsChecks
