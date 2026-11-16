module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ListSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ListBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (emb)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261115 Lists ListSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open InternalApplicationStepPeelSupportProof (andLeft andRight)
theorem introduce (n : Nat) (list bound fuel types heads labels tupleBound : OTerm alpha)
    (h : Nonempty (Derivation body (Delta.map (fun q => q.relabel Sum.inl)) (matrix n list bound fuel types heads labels tupleBound))) :
    Nonempty (Derivation body Delta (Characterizes n list bound fuel types heads labels tupleBound)) :=
  InternalClosedProgramsBindingProof.introduction body alpha 1 Delta _ h

theorem atRaw (n : Nat) (list bound fuel types heads labels tupleBound raw : OTerm alpha)
    (h : Nonempty (Derivation body Delta (Characterizes n list bound fuel types heads labels tupleBound))) :
    (Nonempty (Derivation body Delta (graph2 contains (numeral 1) list raw)) ↔
     Nonempty (Derivation body Delta (Meaning.holds n raw bound fuel types heads labels tupleBound))) := by
  have hw := InternalClosedProgramsBindingProof.elimination body alpha 1 Delta
    (matrix n list bound fuel types heads labels tupleBound) (fun _ => emb raw) h
  rw [matrixWitness] at hw
  constructor
  · intro hm
    exact ⟨Derivation.implicationElimination (Classical.choice (andLeft hw)) (Classical.choice hm)⟩
  · intro hm
    exact ⟨Derivation.implicationElimination (Classical.choice (andRight hw)) (Classical.choice hm)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ListBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ListBindingProof
