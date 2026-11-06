module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.SpecializationDefinitions
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.UndecidabilityTargets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.BareHardnessCompletion.MRDPFamilyTargets
open DiophantineCompletion DiophantineCompletion.Specialization

/-- One finite genuine integer polynomial is chosen for each fixed RE
predicate. Its first coordinate is specialized by the existing total
computable code program. Every resulting instance is well formed, including
inputs outside the predicate. No code extraction from an extensional proof
is asserted, and no representation or undecidability premise is assumed. -/
def REPolynomialFamily : Prop :=
  ∀ (P : Nat → Prop), REPred P →
    ∃ (m : Nat) (p : PolynomialCircuit.Code),
      p.inputCount = m + 1 ∧ p.WellFormed ∧
      (∀ x, (specialize x p).WellFormed) ∧
      Computable (specializationCode p) ∧
      (∀ x, specializationCode p x =
        Encodable.encode (PolynomialCircuit.encode (specialize x p))) ∧
      ∀ x, P x ↔ PolynomialDomainShift.HasNonnegativeRoot (specialize x p)

/-- The existing actual ordinary-code halting predicate supplies the
undecidability witness, with its RE and noncomputability facts both proved. -/
def HaltingObstruction : Prop :=
  DiophantineCompletion.UndecidabilityTargets.NatHaltingRE ∧
    DiophantineCompletion.UndecidabilityTargets.NatHaltingUndecidable

end LogicLineages.ComputabilityKnowledge.BareHardnessCompletion.MRDPFamilyTargets
