module
public import LogicLineages.PersistentMarking.NumberedWindowInternalGuardedMatchedPathTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

import LogicLineages.PersistentMarking.NumberedWindowInternalCoveredFormationChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderArithmeticProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalGuardedMatchedPathChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalClosedPrograms (allBlock)
open ID1Completion.InternalListInductionSyntaxProof (allBlockRename)
open ID1Completion.InternalBinderTransportProof (actualRelabelSubstitution)
open ID1Completion.InternalBinderTransportSyntaxProof (formulaSubstVar)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
private theorem openFresh {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (p : Formula (α ⊕ Fin 1)) (h : Nonempty (Derivation body Γ (allBlock p))) :
    Nonempty (Derivation body (Γ.map (fun q => q.relabel Sum.inl)) p) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let Δ := Γ.map (fun q => q.relabel j)
  have moved := renameInto h j Δ (by intro q hq; exact List.mem_map.mpr ⟨q,hq,rfl⟩)
  rw [allBlockRename] at moved
  obtain ⟨out⟩ := ID1Completion.InternalClosedProgramsBindingProof.elimination body _ 1 Δ
    (p.relabel (Sum.map j id)) (fun i => .var (.inr i)) moved
  rw [actualRelabelSubstitution] at out
  have identity : (fun x : α ⊕ Fin 1 => Sum.elim Term.var (fun i => Term.var (Sum.inr i)) (Sum.map j id x)) =
      (Term.var : α ⊕ Fin 1 → Term (α ⊕ Fin 1)) := by
    funext x
    cases x <;> rfl
  change Derivation body Δ (p.subst (fun x => Sum.elim Term.var (fun i => Term.var (Sum.inr i)) (Sum.map j id x))) at out
  rw [identity,formulaSubstVar] at out
  exact ⟨out⟩

open NumberedWindowInternalGuardedMatchedPathTargets
open NumberedWindowInternalCoveredFormationChecks (exact_CoveredFormation)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename rawConsRename)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparseCoverOccurrenceTargets (occursInCover)
open NumberedWindowInternalSparseFormationRepresentativeTargets (formation)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)

theorem exact_GuardedFormation : ExactGuardedFormation := by
  intro baseV M G s intrinsicBase T body α Γ ctx dom cod arg V C K W
  let S := support C s W T ctx dom cod arg
  let j : α → α ⊕ Fin 1 := Sum.inl
  let f : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let parent := auxiliaryTerm (dom.relabel j) (cod.relabel j) f (arg.relabel j)
  let A := windowAt W (ctx.relabel j) ((rawCons dom cod).relabel j) f
  let R := A.imp (occursInCover C s parent parent)
  let Δ := (S :: Γ).map weaken
  let Θ := A :: Δ
  have h : Derivation body (S :: Γ) S := Derivation.hypothesis List.mem_cons_self
  obtain ⟨original⟩ := openFresh R ⟨Derivation.conjunctionRight h⟩
  obtain ⟨available⟩ := ID1Completion.InternalOriginalPairingOrderArithmeticProof.withHyp ⟨original⟩ A
  have fn : Derivation body Θ A := Derivation.hypothesis List.mem_cons_self
  have occurrence := Derivation.implicationElimination available fn
  have params := renameInto ⟨Derivation.conjunctionLeft h⟩ j Θ
    (by intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  simp only [conjunctionRename,unaryRename,sucRelabel,zRelabel,windowRename] at params
  obtain ⟨params⟩ := params
  obtain ⟨formed⟩ := exact_CoveredFormation baseV M G s intrinsicBase T body _ Θ
    (ctx.relabel j) (dom.relabel j) (cod.relabel j) f (arg.relabel j)
  have child : Derivation body Θ (windowAt W (ctx.relabel j) (rawCons (dom.relabel j) (cod.relabel j)) f) := by
    simpa only [A,rawConsRename] using fn
  have parentWindow := Derivation.implicationElimination formed (Derivation.conjunctionIntroduction
    (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft params)
      (Derivation.conjunctionIntroduction child (Derivation.conjunctionRight params))) occurrence)
  exact ⟨Derivation.implicationIntroduction (Derivation.universalIntroduction
    (Derivation.implicationIntroduction parentWindow))⟩

theorem exact_GuardedPath : ExactGuardedPath := by
  intro baseV M G s intrinsicBase T X raw V C K W law body α Γ ctx dom cod arg fn next cert value positive later
  let S := support C s W T ctx dom cod arg
  let A := S ⊓ (positive ⊓ later)
  let Δ := A :: Γ
  have h : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  obtain ⟨formed⟩ := exact_GuardedFormation baseV M G s intrinsicBase T body α Δ ctx dom cod arg
  obtain ⟨result⟩ := law body α Δ ctx dom cod arg fn next cert value
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination result
    (Derivation.conjunctionIntroduction (Derivation.implicationElimination formed (Derivation.conjunctionLeft h))
      (Derivation.conjunctionRight h)))⟩

#print axioms exact_GuardedFormation
#print axioms exact_GuardedPath
end LogicLineages.PersistentMarking.NumberedWindowInternalGuardedMatchedPathChecks
