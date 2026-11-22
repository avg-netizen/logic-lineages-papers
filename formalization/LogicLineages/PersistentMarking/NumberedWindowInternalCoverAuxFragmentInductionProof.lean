module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentInductionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentInductionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentInductionLocalProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentInductionStepProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentInductionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb suc z sucRelabel zRelabel)
open ID1Completion.InternalClosedPrograms (allBlock)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction)
open ID1Completion.InternalStrongInduction (below lift)
open ID1Completion.InternalStrongInductionProof (actualStrongInductionInstance)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalCoverNumberedTypeWindowTargets (numberedTypeWindow)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (lambdaLexicalWindow)
open NumberedWindowInternalCoverAuxFragmentGuardTargets (fragmentGuard)
open NumberedWindowInternalCoverAuxFragmentInductionSyntaxTargets
open NumberedWindowInternalCoverAuxFragmentInductionSyntaxProof (forwardBelowRename forwardMotiveLift forwardMotiveAt)
open NumberedWindowInternalCoverAuxFragmentInductionLocalProof (selectForwardResult)
open NumberedWindowInternalCoverAuxFragmentInductionStepProof (exact_OpenCoverAuxFragmentInductionStep)
open NumberedWindowInternalCoverAuxFragmentInductionTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private def PointStep (P Q : Program 3) (body : Positive (Fin 1)) : Prop :=
  ∀ (β : Type) (Δ : List (Formula β)) (ctx raw result : OTerm β),
    Nonempty (Derivation body Δ (forwardBelow P Q ctx raw)) →
    Nonempty (Derivation body Δ (unary fragmentGuard (suc z) raw)) →
    Nonempty (Derivation body Δ (windowAt P ctx result raw)) →
    Nonempty (Derivation body Δ (windowAt Q ctx result raw))

private theorem allAtKey (P Q : Program 3) (ctx raw : OTerm α)
    (work : PointStep P Q body)
    (small : Nonempty (Derivation body Γ (forwardBelow P Q ctx raw)))
    (valid : Nonempty (Derivation body Γ (unary fragmentGuard (suc z) raw))) :
    Nonempty (Derivation body Γ (allBlock (forwardMatrix P Q ctx raw))) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let result : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let c := ctx.relabel j
  let key := raw.relabel j
  let old := windowAt P c result key
  let D : List (Formula (α ⊕ Fin 1)) := Γ.map (fun f => f.relabel j)
  let E : List (Formula (α ⊕ Fin 1)) := old :: D
  have keep : ∀ f ∈ Γ, f.relabel j ∈ E := by
    intro f hf
    exact List.mem_cons_of_mem old (List.mem_map.mpr ⟨f,hf,rfl⟩)
  have prior := renameInto small j E keep
  rw [forwardBelowRename] at prior
  have guard := renameInto valid j E keep
  simp only [unaryRename,sucRelabel,zRelabel] at guard
  have before : Nonempty (Derivation body E old) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨after⟩ := work (α ⊕ Fin 1) E c key result prior guard before
  have instanceAtResult : Nonempty (Derivation body D (forwardMatrix P Q ctx raw)) :=
    ⟨Derivation.implicationIntroduction after⟩
  exact actualFiniteUniversalIntroduction body α 1 Γ (forwardMatrix P Q ctx raw) instanceAtResult

private theorem fromStep (P Q : Program 3) (ctx raw result : OTerm α)
    (work : PointStep P Q body)
    (valid : Nonempty (Derivation body Γ (unary fragmentGuard (suc z) raw)))
    (old : Nonempty (Derivation body Γ (windowAt P ctx result raw))) :
    Nonempty (Derivation body Γ (windowAt Q ctx result raw)) := by
  let θ := forwardMotive P Q ctx
  let key : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let c := ctx.relabel Sum.inl
  let H : Formula (α ⊕ Fin 1) := below (lift θ) key
  let D : List (Formula (α ⊕ Fin 1)) := H :: Γ.map weaken
  let A : Formula (α ⊕ Fin 1) := unary fragmentGuard (suc z) key
  have prior : Nonempty (Derivation body (A :: D) (forwardBelow P Q c key)) := by
    have h : Derivation body (A :: D) H :=
      Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
    change Derivation body (A :: D) (below (lift (forwardMotive P Q ctx)) key) at h
    rw [forwardMotiveLift] at h
    exact ⟨h⟩
  have actual : Nonempty (Derivation body (A :: D) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have oneStep : Nonempty (Derivation body D θ) := by
    obtain ⟨yes⟩ := allAtKey P Q c key work prior actual
    exact ⟨Derivation.implicationIntroduction yes⟩
  obtain ⟨proved⟩ := actualStrongInductionInstance body α Γ θ raw oneStep
  change Derivation body Γ (instantiate (forwardMotive P Q ctx) (emb raw)) at proved
  rw [forwardMotiveAt] at proved
  obtain ⟨valid⟩ := valid
  exact selectForwardResult P Q ctx raw result ⟨Derivation.implicationElimination proved valid⟩ old

theorem exact_OpenCoverAuxFragmentWindowForward : ExactOpenCoverAuxFragmentWindowForward := by
  intro s B T body α Γ ctx raw result valid old
  let P : Program 3 := numberedTypeWindow s B T
  let Q : Program 3 := lambdaLexicalWindow s B T
  have work : PointStep P Q body :=
    fun β Δ c key ty => exact_OpenCoverAuxFragmentInductionStep s B T body β Δ c key ty
  exact fromStep P Q ctx raw result work valid old

#print axioms exact_OpenCoverAuxFragmentWindowForward

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentInductionProof
