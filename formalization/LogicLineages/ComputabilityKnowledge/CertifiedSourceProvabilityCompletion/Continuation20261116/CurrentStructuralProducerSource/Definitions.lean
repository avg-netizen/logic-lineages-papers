module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerSource.RetainedExtraProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerSource
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
/-- Q is fixed before source selection and may depend only on the selected
old logical/arithmetic/axiom leaf ASTs. It cannot inspect new pF/pR/c or tags. -/
def extendedExtra {k n : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (Q : Program 1 → Program 1 → Program 3 → Program n)
 (old a : Program 1) (baseX : Program 3) : Program 6 :=
 ReflexivityInstalled.bundle
  [⟨6,CumulativePropositionalSource.extra f lhs rhs t old a baseX⟩,
   ⟨6,CurrentStructuralProducerInventory.carrier f lhs rhs t old a baseX (Q old a baseX)⟩]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerSource
