module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellSuccessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel sucRelabel)
open ID1Completion.InternalOriginalOrderSyntaxProof (addRelabel)
open ID1Completion.InternalBetaDivisionSyntaxProof (mulRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparsePathEnvelope
open NumberedWindowInternalSparsePathEnvelopeTargets

theorem unaryRename {α β : Type} (p : Program 1) (o n : OTerm α) (j : α → β) :
    (unary p o n).relabel j = unary p (o.relabel j) (n.relabel j) :=
  NumberedWindowInternalSparseDecodeSyntaxProof.unaryRename p o n j

theorem inputsRename {α β : Type} (n : OTerm α) (j : α → β) :
    (fun i : Fin 1 => ((![n] : Fin 1 → OTerm α) i).relabel j) = ![n.relabel j] :=
  NumberedWindowInternalSparseDecodeSyntaxProof.unaryInputsRename n j

def packedBody {α : Type} : List (OTerm α) → OTerm α
  | [] => z
  | h::xs => rawCons h (packedBody xs)

theorem rawConsRename {α β : Type} (x y : OTerm α) (j : α → β) :
    (rawCons x y).relabel j = rawCons (x.relabel j) (y.relabel j) := by
  unfold rawCons pairTerm
  simp only [sucRelabel,addRelabel,mulRelabel]

theorem packedBodyRename {α β : Type} (xs : List (OTerm α)) (j : α → β) :
    (packedBody xs).relabel j = packedBody (xs.map (fun t => t.relabel j)) := by
  induction xs with
  | nil => exact zRelabel j
  | cons x xs ih => simp only [packedBody,rawConsRename,ih,List.map_cons]

theorem edgeCodeRename {α β : Type} (q w r : OTerm α) (j : α → β) :
    (edgeCodeTerm q w r).relabel j = edgeCodeTerm (q.relabel j) (w.relabel j) (r.relabel j) := by
  simp only [edgeCodeTerm,rawConsRename,sucRelabel,zRelabel]

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem makeUnary (p q : Program 1) (o n value : OTerm α)
    (outer : Nonempty (Derivation body Γ (unary p o value)))
    (inner : Nonempty (Derivation body Γ (unary q value n))) :
    Nonempty (Derivation body Γ (unary (applyUnary p q) o n)) := by
  apply compositionValue p (fun _ : Fin 1 => q) o ![n] ![value] outer
  intro j
  obtain rfl := Fin.eq_zero j
  exact inner

theorem takeUnary (p q : Program 1) (o n value : OTerm α)
    (main : Nonempty (Derivation body Γ (unary (applyUnary p q) o n)))
    (inner : Nonempty (Derivation body Γ (unary q value n))) :
    Nonempty (Derivation body Γ (unary p o value)) := by
  apply compositionRecover p (fun _ : Fin 1 => q) o ![n] ![value] main
  intro j
  obtain rfl := Fin.eq_zero j
  exact inner

theorem moveReport {β : Type} (j : α → β) (Δ : List (Formula β))
    (hJ : ∀ p ∈ Γ, p.relabel j ∈ Δ) (p : Program 1) (o n : OTerm α)
    (h : Nonempty (Derivation body Γ (unary p o n))) :
    Nonempty (Derivation body Δ (unary p (o.relabel j) (n.relabel j))) := by
  have v := renameInto h j Δ hJ
  rw [unaryRename] at v
  exact v

/-- The ordered positions are the genuine sequential raw selector calls,
not assorted equalities between native values. -/
def Reports (body : Positive (Fin 1)) (Γ : List (Formula α)) (root : OTerm α)
    (src : Program 1) : List (OTerm α) → Prop
  | [] => True
  | x::xs =>
    Nonempty (Derivation body Γ (unary (applyUnary cellHead src) x root)) ∧
      Reports body Γ root (applyUnary cellTail src) xs

theorem moveReports {β : Type} (j : α → β) (Δ : List (Formula β))
    (hJ : ∀ p ∈ Γ, p.relabel j ∈ Δ) (root : OTerm α) (src : Program 1) (xs : List (OTerm α))
    (h : Reports body Γ root src xs) :
    Reports body Δ (root.relabel j) src (xs.map (fun t => t.relabel j)) := by
  induction xs generalizing src with
  | nil => trivial
  | cons x xs ih =>
    exact ⟨moveReport j Δ hJ _ x root h.1, ih _ h.2⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
