module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationIntroductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open OriginalRawSyntaxTransportInternalCancellation OriginalRawSyntaxTransportInternalCancellationBindingProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atRawIntroFrom (p q : Program 3) (raw : OTerm alpha)
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (d k shifted : OTerm beta),
      (∀ r ∈ Delta, r.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph3 p shifted (numeral 0) k (raw.relabel j))) →
      Nonempty (Derivation body Theta (graph3 q (raw.relabel j) d k shifted))) :
    Nonempty (Derivation body Delta (AtRaw p q raw)) := by
  let d : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
  let k : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
  let shifted : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
  let A := graph3 p shifted (numeral 0) k (raw.relabel Sum.inl)
  let Theta := A :: Delta.map (fun r => r.relabel Sum.inl)
  obtain ⟨h⟩ := step (alpha ⊕ Fin 3) Sum.inl Theta d k shifted
    (by intro r hr; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨r,hr,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact atRawIntro p q raw ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationIntroductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationIntroductionProof
