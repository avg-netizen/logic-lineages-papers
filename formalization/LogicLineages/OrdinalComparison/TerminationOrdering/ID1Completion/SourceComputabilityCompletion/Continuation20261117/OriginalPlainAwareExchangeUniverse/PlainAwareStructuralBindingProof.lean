module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.PlainAwareStructuralSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.PlainAwareStructuralBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (emb)
open SourceComputabilityFormulaSupportProof
open PlainAwareStructuralDefinitions PlainAwareStructuralSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
theorem transferApply (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
 (mode : Bool) (source target typ gamma context : OTerm alpha)
 (h : Nonempty (Derivation body Delta (Transfer n arity M W mode source target context)))
 (ha : Nonempty (Derivation body Delta (Checked n arity M W mode typ source gamma context)))
 (hp : Nonempty (Derivation body Delta (Plain n arity mode typ target gamma))) :
 Nonempty (Derivation body Delta (Checked n arity M W mode typ target gamma context)) := by
 obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 2 Delta
  (TransferMatrix n arity M W mode source target context) (fun i => emb (![typ,gamma] i)) h
 rw [matrixWitness] at h
 obtain ⟨hh⟩ := andIntro ha hp
 exact ⟨Derivation.implicationElimination h hh⟩

theorem transferIntro (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
 (mode : Bool) (source target context : OTerm alpha)
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (typ gamma : OTerm beta),
  (∀ q ∈ Delta, q.relabel j ∈ Theta) →
  Nonempty (Derivation body Theta (Checked n arity M W mode typ (source.relabel j) gamma (context.relabel j))) →
  Nonempty (Derivation body Theta (Plain n arity mode typ (target.relabel j) gamma)) →
  Nonempty (Derivation body Theta (Checked n arity M W mode typ (target.relabel j) gamma (context.relabel j)))) :
 Nonempty (Derivation body Delta (Transfer n arity M W mode source target context)) := by
 apply InternalClosedProgramsBindingProof.introduction body alpha 2 Delta
 let v : Fin 2 → OTerm (alpha ⊕ Fin 2) := fun i => .var (.inr i)
 let A := (Checked n arity M W mode (v 0) (source.relabel Sum.inl) (v 1) (context.relabel Sum.inl)) ⊓
  (Plain n arity mode (v 0) (target.relabel Sum.inl) (v 1))
 let Theta := A :: Delta.map (fun q => q.relabel (Sum.inl : alpha → alpha ⊕ Fin 2))
 have hh : Nonempty (Derivation body Theta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨h⟩ := next (alpha ⊕ Fin 2) Sum.inl Theta (v 0) (v 1)
  (fun q hq => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)) (andLeft hh) (andRight hh)
 exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.PlainAwareStructuralBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.PlainAwareStructuralBindingProof
