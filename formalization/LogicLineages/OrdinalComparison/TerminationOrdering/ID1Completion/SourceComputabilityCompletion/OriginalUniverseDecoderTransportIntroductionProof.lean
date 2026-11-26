module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportIntroductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open OriginalContextInsertion OriginalRawSyntaxTransport
open OriginalTypedDecoderTransport (selectedMode sourceContext targetContext)
open OriginalUniverseDecoderTransport OriginalUniverseDecoderTransportBindingProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atRawIntroFrom (H : Program 1) (M W : Program 2) (erasing : Bool) (raw : OTerm alpha)
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (arguments : Bool) (d cutoff gamma extended typ transformed c : OTerm beta),
      (∀ r ∈ Delta, r.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (Insert d cutoff gamma extended)) →
      Nonempty (Derivation body Theta
        (graph3 (fold (selectedMode erasing)) transformed d cutoff (raw.relabel j))) →
      Nonempty (Derivation body Theta
        (Accepted H M W arguments typ (raw.relabel j) (sourceContext erasing gamma extended) c)) →
      Nonempty (Derivation body Theta
        (Accepted H M W arguments typ transformed (targetContext erasing gamma extended) c))) :
    Nonempty (Derivation body Delta (AtRaw H M W erasing raw)) := by
  let v : Fin 7 → OTerm (alpha ⊕ Fin 7) := fun i => .var (.inr i)
  have one (arguments : Bool) : Nonempty (Derivation body
      (Delta.map (fun r => r.relabel Sum.inl))
      (Transport H M W erasing arguments (v 0) (v 1) (v 2) (v 3) (v 4)
        (raw.relabel Sum.inl) (v 5) (v 6))) := by
    let A := Insert (v 0) (v 1) (v 2) (v 3) ⊓
      (graph3 (fold (selectedMode erasing)) (v 5) (v 0) (v 1) (raw.relabel Sum.inl) ⊓
        Accepted H M W arguments (v 4) (raw.relabel Sum.inl) (sourceContext erasing (v 2) (v 3)) (v 6))
    let Theta := A :: Delta.map (fun r => r.relabel Sum.inl)
    have h : Derivation body Theta A := Derivation.hypothesis List.mem_cons_self
    obtain ⟨out⟩ := step (alpha ⊕ Fin 7) Sum.inl Theta arguments (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)
      (by intro r hr; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨r,hr,rfl⟩))
      ⟨Derivation.conjunctionLeft h⟩
      ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight h)⟩
      ⟨Derivation.conjunctionRight (Derivation.conjunctionRight h)⟩
    exact ⟨Derivation.implicationIntroduction out⟩
  obtain ⟨ht⟩ := one false
  obtain ⟨ha⟩ := one true
  exact atRawIntro H M W erasing raw ⟨Derivation.conjunctionIntroduction ht ha⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportIntroductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportIntroductionProof
