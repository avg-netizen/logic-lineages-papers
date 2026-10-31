module
public import LogicLineages.OrdinalComparison.WWOriginalInputDomainTargets
public import LogicLineages.OrdinalComparison.WWGroundTupleProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalInput
open ForwardTranslation

theorem originalInputCodecCorrect : Targets.OriginalInputCodecCorrect := by
  constructor
  · intro q
    simp [decode]
  · exact Primrec.option_getD.comp Primrec.decode (Primrec.const (0, false, 7, 7))

theorem originalInputUniversalTupleEquivalence : Targets.OriginalInputUniversalTupleEquivalence := by
  intro q
  have hg : ∀ σ ∈ context q, σ = Ty.ground := by
    intro σ hσ
    exact (List.mem_replicate.mp hσ).2
  constructor
  · intro h xs hlen τ υ a b av bv ha hb hav hbv
    exact h τ υ a b av bv ha hb hav hbv _ (groundTuplePositive (context q) xs)
  · intro h τ υ a b av bv ha hb hav hbv ρ hρ
    obtain ⟨xs, hlen, hx⟩ := groundPositiveTupleComplete (context q) hg ρ hρ
    have hv := h xs (by simpa [context] using hlen) τ υ a b av bv ha hb hav hbv
    have he : (fun c => xs.getD (SourceTypedPorts.variableIndex c.2.1) 0 + 1) = ρ := funext hx
    rwa [he] at hv
end LogicLineages.OrdinalComparison.Source.OriginalInput
