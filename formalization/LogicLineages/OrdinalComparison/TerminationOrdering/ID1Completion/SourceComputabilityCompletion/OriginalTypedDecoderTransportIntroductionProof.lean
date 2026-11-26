module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportIntroductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open OriginalContextInsertion OriginalRawSyntaxTransport
open OriginalTypedDecoderTransport OriginalTypedDecoderTransportBindingProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atRawIntroFrom (H : Program 1) (erasing : Bool) (raw : OTerm alpha)
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (arguments : Bool) (d cutoff gamma extended typ transformed : OTerm beta),
      (∀ r ∈ Delta, r.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (Insert d cutoff gamma extended)) →
      Nonempty (Derivation body Theta
        (graph3 (fold (selectedMode erasing)) transformed d cutoff (raw.relabel j))) →
      Nonempty (Derivation body Theta
        (Accepted H arguments typ (raw.relabel j) (sourceContext erasing gamma extended))) →
      Nonempty (Derivation body Theta
        (Accepted H arguments typ transformed (targetContext erasing gamma extended)))) :
    Nonempty (Derivation body Delta (AtRaw H erasing raw)) := by
  let v : Fin 6 → OTerm (alpha ⊕ Fin 6) := fun i => .var (.inr i)
  have one (arguments : Bool) : Nonempty (Derivation body
      (Delta.map (fun r => r.relabel Sum.inl))
      (Transport H erasing arguments (v 0) (v 1) (v 2) (v 3) (v 4)
        (raw.relabel Sum.inl) (v 5))) := by
    let A := Insert (v 0) (v 1) (v 2) (v 3) ⊓
      (graph3 (fold (selectedMode erasing)) (v 5) (v 0) (v 1) (raw.relabel Sum.inl) ⊓
        Accepted H arguments (v 4) (raw.relabel Sum.inl) (sourceContext erasing (v 2) (v 3)))
    let Theta := A :: Delta.map (fun r => r.relabel Sum.inl)
    have h : Derivation body Theta A := Derivation.hypothesis List.mem_cons_self
    obtain ⟨out⟩ := step (alpha ⊕ Fin 6) Sum.inl Theta arguments (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)
      (by intro r hr; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨r,hr,rfl⟩))
      ⟨Derivation.conjunctionLeft h⟩
      ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight h)⟩
      ⟨Derivation.conjunctionRight (Derivation.conjunctionRight h)⟩
    exact ⟨Derivation.implicationIntroduction out⟩
  obtain ⟨ht⟩ := one false
  obtain ⟨ha⟩ := one true
  exact atRawIntro H erasing raw ⟨Derivation.conjunctionIntroduction ht ha⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportIntroductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportIntroductionProof
