module
public import LogicLineages.StandardControlCurrent.PolynomialBoolean.ExistentialProof
public import LogicLineages.StandardControlCurrent.PolynomialBoolean.CalibrationProof
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineCorrectnessProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolynomialBoolean.DecisionProof
open OrdinalComparison WordLinearDecisionCompletion

/-- Both flags query the literal matrix. Only the output test, never the
positive graph constraints, is complemented for the universal flag. -/
theorem flags (d : Nat) (p : Source) (hv : p.Valid d) :
    ((Code.flags d (sourceCode p)).1 = true ↔ ∃ ρ, Positive d ρ ∧ p.eval ρ) ∧
    ((Code.flags d (sourceCode p)).2 = true ↔ ∀ ρ, Positive d ρ → p.eval ρ) := by
  classical
  have hd := DomainsProof.full d p hv
  have he := ClosedWordDecisionCompletion.MachineProof.actualClosedDecision
    p.degree (matrix d p false) (hd.2 false).1
  have hc := ClosedWordDecisionCompletion.MachineProof.actualClosedDecision
    p.degree (matrix d p true) (hd.2 true).1
  have ex := he.trans (ExistentialProof.full d p hv).1
  have counter := hc.trans (ExistentialProof.full d p hv).2
  simp only [Code.flags, CalibrationProof.full]
  constructor
  · exact ex
  · rw [Bool.not_eq_true]
    constructor
    · intro h ρ hp
      by_contra hn
      have ht := counter.mpr ⟨ρ,hp,hn⟩
      rw [h] at ht
      contradiction
    · intro h
      cases hb : ClosedWordDecisionCompletion.Machine.solve p.degree
          (Formula.encode (matrix d p true))
      · rfl
      · obtain ⟨ρ,hp,hn⟩ := counter.mp hb
        exact False.elim (hn (h ρ hp))

end LogicLineages.StandardControlCurrent.PolynomialBoolean.DecisionProof
