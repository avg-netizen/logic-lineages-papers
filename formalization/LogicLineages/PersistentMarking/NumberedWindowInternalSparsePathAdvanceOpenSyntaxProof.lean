module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceOpenSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue successorValue programRename)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue oneConstantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelope (hopTarget)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary z suc)
open NumberedWindowInternalSparsePathAdvance

abbrev coords {α : Type} (c ty s h : OTerm α) : Fin 4 → OTerm α := ![c,ty,s,h]

theorem coordsRename {α β : Type} (c ty s h : OTerm α) (j : α → β) :
    (fun i => (coords c ty s h i).relabel j) =
      coords (c.relabel j) (ty.relabel j) (s.relabel j) (h.relabel j) := by
  funext i
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun l =>
    Fin.cases ?_ (fun m => Fin.cases ?_ (fun u => Fin.elim0 u) m) l) k) i <;> rfl

theorem quadRename {α β : Type} (p : Program 4) (o c t s h : OTerm α) (j : α → β) :
    (programGraph p o (coords c t s h)).relabel j =
      programGraph p (o.relabel j) (coords (c.relabel j) (t.relabel j) (s.relabel j) (h.relabel j)) := by
  rw [programRename,coordsRename]

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem moveQuad {β : Type} (j : α → β) (Δ : List (Formula β))
    (hJ : ∀ p ∈ Γ, p.relabel j ∈ Δ) (p : Program 4) (o c t s h : OTerm α)
    (pGraph : Nonempty (Derivation body Γ (programGraph p o (coords c t s h)))) :
    Nonempty (Derivation body Δ
      (programGraph p (o.relabel j) (coords (c.relabel j) (t.relabel j) (s.relabel j) (h.relabel j)))) := by
  have next := renameInto pGraph j Δ hJ
  rw [quadRename] at next
  exact next

theorem atHopIntro (p : Program 1) (o c ty s h : OTerm α)
    (hp : Nonempty (Derivation body Γ (unary p o h))) :
    Nonempty (Derivation body Γ (programGraph (atHop p) o (coords c ty s h))) := by
  apply compositionValue p (fun _ : Fin 1 => .projection 3) o (coords c ty s h) ![h] hp
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue (3 : Fin 4) (coords c ty s h)

theorem stateZero (c ty h : OTerm α) :
    Nonempty (Derivation body Γ (programGraph statePresent z (coords c ty z h))) :=
  zeroBranchIntro (.projection 2) (constantZero 4) (constantOne 4) z (coords c ty z h)
    (projectionValue (2 : Fin 4) (coords c ty z h)) (zeroConstantValue (coords c ty z h))

theorem stateSucc (c ty s h : OTerm α) :
    Nonempty (Derivation body Γ (programGraph statePresent (suc z) (coords c ty (suc s) h))) :=
  successorBranchIntro (.projection 2) (constantZero 4) (constantOne 4) (suc z) s
    (coords c ty (suc s) h) (projectionValue (2 : Fin 4) (coords c ty (suc s) h))
    (oneConstantValue (coords c ty (suc s) h))

theorem targetGraph (o c ty s h : OTerm α)
    (hp : Nonempty (Derivation body Γ (programGraph (atHop hopTarget) o (coords c ty s h)))) :
    Nonempty (Derivation body Γ (programGraph targetCode (suc o) (coords c ty s h))) := by
  apply compositionValue .succ (fun _ : Fin 1 => atHop hopTarget)
    (suc o) (coords c ty s h) ![o] (successorValue ![o])
  intro i
  obtain rfl := Fin.eq_zero i
  exact hp

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceOpenSyntaxProof
