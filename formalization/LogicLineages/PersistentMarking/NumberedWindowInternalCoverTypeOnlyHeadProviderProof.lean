module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeOnlyArgumentListTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafSharedMeasureProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeavesOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarTypeLeafStageProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthObservationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeOnlyHeadProviderProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (projectionValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel eqnRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldCellSyntaxProof (moveUnary)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (grammarTypeAt)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (leafTypeTest)
open NumberedWindowInternalCoverTypeLeavesTargets (typeLeafTerm)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverHeaderFieldsOpenProof (exact_OpenCoverHeaderFields)
open NumberedWindowInternalCoverTypeLeafMeasureTargets (typeLeafSharedMeasure)
open NumberedWindowInternalCoverTypeLeafSharedMeasureProof (exact_OpenCoverTypeLeafSharedMeasure)
open NumberedWindowInternalCoverSelectedGrammarTypeLeafStageProof (exact_OpenSelectedGrammarTypeLeafAtSuccessor)
open NumberedWindowInternalCoverSelectedGrammarWidthObservationProof (observationCases)
open NumberedWindowInternalCoverSharedOwnScratchTargets (OwnOccurrence)
open NumberedWindowInternalCoverRefinedInductionDispatchTransportProof (moveMemberKey)
open NumberedWindowInternalCoverMeasuredDispatchRenameProof (moveStoredK keepThrough)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (pairRename)
open NumberedWindowInternalCoverArgumentGrammarInductionTargets (HeadProvider)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalCoverTypeOnlyArgumentListTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem actualMember (s : Settings) (raw ty : OTerm α)
    (selected : Nonempty (Derivation body Γ (unary (field 0) ty raw)))
    (yes : Nonempty (Derivation body Γ (unary (leafTypeTest s) (suc z) raw))) :
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty)) := by
  have finite : Nonempty (Derivation body Γ (unary (grammarTypeAt s) (suc z) ty)) := by
    apply compositionRecover (grammarTypeAt s) (fun _ : Fin 1 => field 0) (suc z) ![raw] ![ty] yes
    intro i
    obtain rfl := Fin.eq_zero i
    exact selected
  let k := Encodable.encode s.types
  apply compositionRecover scratchMember ![literal 1 k,.projection 0] (suc z)
    ![ty] ![numeral k,ty] finite
  intro i
  exact Fin.cases (literalGraph k ![ty])
    (Fin.cases (projectionValue 0 ![ty]) (fun j => Fin.elim0 j)) i

private theorem sourceAtType (s : Settings) (M : Program 1) (raw ty p : OTerm α) (Q : Formula α)
    (eq : Nonempty (Derivation body Γ (eqn raw (typeLeafTerm ty))))
    (member : Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty)))
    (measured : Nonempty (Derivation body Γ (unary (typeLeafSharedMeasure M) p raw)))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (state terms args : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (codePair (p.relabel j) (suc z) z)) →
      OwnOccurrence s body Δ (suc z) z state terms args (raw.relabel j) →
      Nonempty (Derivation body Δ (Q.relabel j))) :
    Nonempty (Derivation body Γ Q) := by
  have literal := moveUnary (typeLeafSharedMeasure M) p raw (typeLeafTerm ty) eq measured
  have pair := exact_OpenCoverTypeLeafSharedMeasure M body α Γ ty p literal
  apply observationCases (suc z) (headsTerm s α) (typesTerm s α) z Q
  intro β j Δ state terms args keep actual
  simp only [headsTerm,typesTerm,numeralRename,sucRelabel,zRelabel] at actual
  have k := moveStoredK s j keep ty member
  have hit := exact_OpenSelectedGrammarTypeLeafAtSuccessor body β Δ z (headsTerm s β) (typesTerm s β)
    z state terms args (ty.relabel j) actual k
  have eq' := renameInto eq j Δ keep
  rw [eqnRelabel,NumberedWindowInternalCoverTypeLeavesOpenDataProof.termRename] at eq'
  obtain ⟨packed⟩ := eq'
  have onRaw := moveMemberKey terms (typeLeafTerm (ty.relabel j)) (raw.relabel j) (symm packed) hit
  have shape := renameInto pair j Δ keep
  simp only [pairRename,sucRelabel,zRelabel] at shape
  exact next β j Δ state terms args keep shape ⟨actual,onRaw⟩

theorem exact_OpenCoverTypeOnlyHeadProvider : ExactOpenCoverTypeOnlyHeadProvider := by
  intro s M body α Γ raw p Q selected measured next
  obtain ⟨checks⟩ := conjunctionRecover (header 3 1) (leafTypeTest s) ![raw] selected
  have kReport : Nonempty (Derivation body Γ (unary (leafTypeTest s) (suc z) raw)) :=
    ⟨Derivation.conjunctionRight checks⟩
  apply exact_OpenCoverHeaderFields 3 1 body α Γ raw Q ⟨Derivation.conjunctionLeft checks⟩
  intro β j Δ fields keep len report packed
  rcases fields with _ | ⟨ty,_ | ⟨head,tail⟩⟩ <;> simp at len
  have check := renameInto kReport j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at check
  have actual := actualMember s (raw.relabel j) ty report.1 check
  have measure := renameInto measured j Δ keep
  rw [unaryRename] at measure
  apply sourceAtType s M (raw.relabel j) ty (p.relabel j) (Q.relabel j) packed actual measure
  intro γ g Ξ state terms args retain pair hit
  simp only [Term.relabel_relabel] at pair hit
  rw [formulaRelabelComposition j g Q]
  exact next γ (g ∘ j) Ξ (suc z) z state terms args (keepThrough j g keep retain) pair hit

#print axioms exact_OpenCoverTypeOnlyHeadProvider

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeOnlyHeadProviderProof
