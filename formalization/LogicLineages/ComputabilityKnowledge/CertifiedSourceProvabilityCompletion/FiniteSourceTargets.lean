module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.FiniteSourceDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.FiniteSource.Targets
open GorbowSyntax GorbowPRProgram GorbowPublishedDCB GorbowTheoryProof

/-- ONE bound precedes all source axioms and ordinary proof contexts, with
an accepted certificate for every source axiom. The last field gives actual closed
source arithmetic derivations. This is not internally quantified variable-
certificate preservation, HB2/HB3, or a completed source-collapse statement. -/
def ActualFixedFuelPackage : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∃ fuel : Nat,
    (∀ sigma : Sentence, S pF pR q sigma ↔
      GorbowEnumeratedProvability.boundedTheory (c, fuel) sigma) ∧
    (∀ n (phi : Formula n),
      Nonempty (Derivation (S pF pR q) phi) ↔
      Nonempty (Derivation (GorbowEnumeratedProvability.boundedTheory (c, fuel)) phi)) ∧
    (∀ sigma : Sentence, S pF pR q sigma →
      ∃ certificate : Nat,
        GorbowEnumeratedProvability.check (c, fuel) 0
          (GorbowSortedSyntaxCode.formulaCode sigma) certificate = true ∧
        Nonempty (Derivation (S pF pR q)
          (checkerEquation pF c fuel (GorbowSortedSyntaxCode.formulaCode sigma) certificate)))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.FiniteSource.Targets
