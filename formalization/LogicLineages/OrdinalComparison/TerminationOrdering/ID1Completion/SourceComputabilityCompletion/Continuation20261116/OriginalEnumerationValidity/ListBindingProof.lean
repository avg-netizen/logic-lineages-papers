module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.ListSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.ListBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (emb)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261115 Lists ListSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem introduce (n : Nat) (list : OTerm alpha)
    (h : Nonempty (Derivation body (Delta.map (fun q => q.relabel Sum.inl)) (matrix n list))) :
    Nonempty (Derivation body Delta (AllValid n list)) :=
  InternalClosedProgramsBindingProof.introduction body alpha 1 Delta _ h

theorem member (n : Nat) (list raw : OTerm alpha)
    (h : Nonempty (Derivation body Delta (AllValid n list)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) list raw))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 1 Delta
    (matrix n list) (fun _ => emb raw) h
  rw [matrixWitness] at h
  exact ⟨Derivation.implicationElimination h (Classical.choice hm)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.ListBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.ListBindingProof
