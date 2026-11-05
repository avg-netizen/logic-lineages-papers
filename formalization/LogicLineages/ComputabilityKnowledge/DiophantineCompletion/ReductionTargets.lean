module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.Targets
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.SpecializationDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.ReductionTargets

/-- Original recursively enumerable predicates, including undefined cases,
on the single natural parameter coordinate. -/
def REPredicateDiophantine : Prop := ∀ P : Nat → Prop, REPred P →
  Dioph {v : Fin 1 → Nat | P (v 0)}

/-- Faithful canonical encoding into the unchanged solvability predicate.
The original natural-zero-root interpretation is preserved exactly. -/
def EncodedCodeRoot : Prop := ∀ p : PolynomialCircuit.Code, p.WellFormed →
  (encodedPolynomialSolvable (Encodable.encode (PolynomialCircuit.encode p)) ↔
    PolynomialDomainShift.HasNonnegativeRoot p)

-- The final comparator is the unchanged Targets.REPolynomialReduction.
-- Its quantifier order chooses one finite representing code for each fixed
-- predicate, then requires a computable natural-input reduction. It does not
-- assert an algorithm extracting codes from extensional representation proofs.
end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.ReductionTargets
