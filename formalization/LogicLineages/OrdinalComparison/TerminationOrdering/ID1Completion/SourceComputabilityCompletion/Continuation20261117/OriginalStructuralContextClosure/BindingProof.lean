module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalStructuralContextClosure.SyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalStructuralContextClosure.BindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (emb)
open SourceComputabilityFormulaSupportProof
open Definitions SyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem transferApply (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (mode : Bool) (source target typ gamma context : OTerm alpha)
    (h : Nonempty (Derivation body Delta (Transfer n arity M W mode source target)))
    (ha : Nonempty (Derivation body Delta (Checked n arity M W mode typ source gamma context))) :
    Nonempty (Derivation body Delta (Checked n arity M W mode typ target gamma context)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 3 Delta
    (TransferMatrix n arity M W mode source target) (fun i => emb (![typ,gamma,context] i)) h
  rw [matrixWitness] at h
  obtain ⟨ha⟩ := ha
  exact ⟨Derivation.implicationElimination h ha⟩

theorem transferIntro (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (mode : Bool) (source target : OTerm alpha)
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (typ gamma context : OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (Checked n arity M W mode typ (source.relabel j) gamma context)) →
      Nonempty (Derivation body Theta (Checked n arity M W mode typ (target.relabel j) gamma context))) :
    Nonempty (Derivation body Delta (Transfer n arity M W mode source target)) := by
  apply InternalClosedProgramsBindingProof.introduction body alpha 3 Delta
  let v : Fin 3 → OTerm (alpha ⊕ Fin 3) := fun i => .var (.inr i)
  let A := Checked n arity M W mode (v 0) (source.relabel Sum.inl) (v 1) (v 2)
  let Theta := A :: Delta.map (fun q => q.relabel (Sum.inl : alpha → alpha ⊕ Fin 3))
  have ha : Nonempty (Derivation body Theta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := next (alpha ⊕ Fin 3) Sum.inl Theta (v 0) (v 1) (v 2)
    (fun q hq => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)) ha
  exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalStructuralContextClosure.BindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalStructuralContextClosure.BindingProof
