module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCompiler.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCompiler.RecurrenceProof
open GorbowSyntax GorbowPRProgram GorbowPRChildTags List.Vector
/-- Pointwise transport of the genuine raw Nat.rec, including every decoder
and default. No well-formedness of the supplied numbers is used. -/
theorem congruence (formula formula' step step' : Nat → Nat) (base base' : Nat)
 (hf : ∀ k, formula k = formula' k) (hs : ∀ k, step k = step' k) (hb : base = base')
 (counter : Nat) :
 CurrentRecursionAccumulator.rawNumber formula step base counter =
 CurrentRecursionAccumulator.rawNumber formula' step' base' counter := by
 induction counter with
 | zero => exact hb
 | succ k ih =>
  simp only [CurrentRecursionAccumulator.rawNumber] at ih ⊢
  rw [hf,hs,ih]

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCompiler.RecurrenceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCompiler.RecurrenceProof
