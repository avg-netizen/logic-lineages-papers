module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectRecognizeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectControlProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc sucRelabel zRelabel)
open ID1Completion.InternalAcceptance (branch conjunction)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalProbeTargets (OTerm)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalAtomicRefinement (atSource freeSource bottomSource)
open NumberedWindowInternalAtomicRefinementObjectTargets (packedBottomTerm)
open NumberedWindowInternalAtomicRefinementObjectRecognizeProof (exactRecognition)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (packedFreeTerm)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalAtomicApplicationShape NumberedWindowInternalAtomicApplicationShapeObjectTargets

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem acceptsGraph (p : Program 3) (f u y : OTerm α) :
    accepts p f u y = programGraph p (suc z) ![f,u,y] := rfl

private theorem chooseAst (p : Program 3) :
    refinedApplication p =
      branch (atSource freeSource) (branch (atSource bottomSource) p (atomBranch p)) (atomBranch p) := by
  unfold refinedApplication
  rw [exact_DispatchControlAST.2.2.2.2.1,exact_DispatchControlAST.2.2.2.2.1]

section
attribute [local irreducible] programGraph

theorem callSlot (p : Program 1) (i : Fin 3) (v : OTerm α) (xs : Fin 3 → OTerm α)
    (h : Nonempty (Derivation B Γ (programGraph p v ![xs i]))) :
    Nonempty (Derivation B Γ (programGraph (.composition p (fun _ : Fin 1 => .projection i)) v xs)) := by
  apply compositionValue p (fun _ : Fin 1 => .projection i) v xs ![xs i] h
  intro k
  obtain rfl := Fin.eq_zero k
  exact projectionValue i xs

private theorem atomParts (p : Program 3) (xs : Fin 3 → OTerm α)
    (h : Nonempty (Derivation B Γ (programGraph (atomBranch p) (suc z) xs))) :
    Nonempty (Derivation B Γ (programGraph p (suc z) xs ⊓ programGraph atomicChecks (suc z) xs)) := by
  rw [atomBranch,exact_DispatchControlAST.2.2.2.2.2] at h
  exact conjunctionRecover p atomicChecks xs h

theorem freeChecks (p : Program 3) (f u y c t n : OTerm α)
    (shape : Nonempty (Derivation B Γ (equal f (packedFreeTerm c t n))))
    (h : Nonempty (Derivation B Γ (accepts (refinedApplication p) f u y))) :
    Nonempty (Derivation B Γ (programGraph atomicChecks (suc z) ![f,u,y])) := by
  let xs : Fin 3 → OTerm α := ![f,u,y]
  obtain ⟨g⟩ := exactRecognition.1 B α Γ f c t n shape
  have hf : Nonempty (Derivation B Γ (programGraph (atSource freeSource) (suc z) xs)) :=
    callSlot freeSource 0 (suc z) xs ⟨Derivation.conjunctionLeft g⟩
  rw [acceptsGraph,chooseAst] at h
  obtain ⟨accepted⟩ := atomParts p xs (successorBranchElim (atSource freeSource)
    (branch (atSource bottomSource) p (atomBranch p)) (atomBranch p) (suc z) z xs hf h)
  exact ⟨Derivation.conjunctionRight accepted⟩

theorem bottomChecks (p : Program 3) (f u y c t : OTerm α)
    (shape : Nonempty (Derivation B Γ (equal f (packedBottomTerm c t))))
    (h : Nonempty (Derivation B Γ (accepts (refinedApplication p) f u y))) :
    Nonempty (Derivation B Γ (programGraph atomicChecks (suc z) ![f,u,y])) := by
  let xs : Fin 3 → OTerm α := ![f,u,y]
  obtain ⟨g⟩ := exactRecognition.2 B α Γ f c t shape
  have hf : Nonempty (Derivation B Γ (programGraph (atSource freeSource) z xs)) :=
    callSlot freeSource 0 z xs ⟨Derivation.conjunctionLeft g⟩
  have hb : Nonempty (Derivation B Γ (programGraph (atSource bottomSource) (suc z) xs)) :=
    callSlot bottomSource 0 (suc z) xs ⟨Derivation.conjunctionRight g⟩
  rw [acceptsGraph,chooseAst] at h
  have inside := zeroBranchElim (atSource freeSource)
    (branch (atSource bottomSource) p (atomBranch p)) (atomBranch p) (suc z) xs hf h
  obtain ⟨accepted⟩ := atomParts p xs (successorBranchElim (atSource bottomSource) p
    (atomBranch p) (suc z) z xs hb inside)
  exact ⟨Derivation.conjunctionRight accepted⟩

private theorem stripBranch (chk a b p : Program 3) (xs : Fin 3 → OTerm α)
    (d : Nonempty (Derivation B Γ (programGraph (branch chk a b) (suc z) xs)))
    (left : ∀ (β : Type) (Δ : List (Formula β)) (ys : Fin 3 → OTerm β),
      Nonempty (Derivation B Δ (programGraph a (suc z) ys)) →
      Nonempty (Derivation B Δ (programGraph p (suc z) ys)))
    (right : ∀ (β : Type) (Δ : List (Formula β)) (ys : Fin 3 → OTerm β),
      Nonempty (Derivation B Δ (programGraph b (suc z) ys)) →
      Nonempty (Derivation B Δ (programGraph p (suc z) ys))) :
    Nonempty (Derivation B Γ (programGraph p (suc z) xs)) := by
  apply optionGraphCases chk xs (programGraph p (suc z) xs)
  · intro β j Δ hj hz
    have moved := renameInto d j Δ hj
    simp only [programRename,sucRelabel,zRelabel] at moved ⊢
    exact left β Δ (fun i => (xs i).relabel j)
      (zeroBranchElim chk a b (suc z) _ hz moved)
  · intro β j Δ v hj hv
    have moved := renameInto d j Δ hj
    simp only [programRename,sucRelabel,zRelabel] at moved ⊢
    exact right β Δ (fun i => (xs i).relabel j)
      (successorBranchElim chk a b (suc z) v _ hv moved)

theorem forgets : ExactOpenApplicationForgets := by
  intro p B α Γ f u y accepted
  rw [acceptsGraph,chooseAst] at accepted
  rw [acceptsGraph]
  have atomImplies : ∀ (β : Type) (Δ : List (Formula β)) (xs : Fin 3 → OTerm β),
      Nonempty (Derivation B Δ (programGraph (atomBranch p) (suc z) xs)) →
      Nonempty (Derivation B Δ (programGraph p (suc z) xs)) := by
    intro β Δ xs h
    obtain ⟨hp⟩ := atomParts p xs h
    exact ⟨Derivation.conjunctionLeft hp⟩
  apply stripBranch (atSource freeSource) (branch (atSource bottomSource) p (atomBranch p))
    (atomBranch p) p ![f,u,y] accepted _ atomImplies
  intro β Δ xs h
  exact stripBranch (atSource bottomSource) p (atomBranch p) p xs h (fun _ _ _ h => h) atomImplies

end

end LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectControlProof
