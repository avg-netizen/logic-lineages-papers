module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.BoundsProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.CoreTools
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.InductionInterface
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence SixSol20261112.Fuel NamedArithmeticGraph
/-- Proof-only strengthened IH: every actual evaluator/compiled producer
occurrence, every context and runtime input, but ONE source/index/fuel bound. -/
def Correct (installed : Formula 1) (lhs rhs : Term 1) {k : Nat} (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code)
 (I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) (bound : Nat)
 {m : Nat} (u : Program m) : Prop :=
 ∀ (target producerTag : Nat),
 (nodes (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX))[target]? = some ⟨m,u⟩ →
 (nodes (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX))[producerTag]? =
  some ⟨m+1,CurrentStructuralProducerCompiler.compile u⟩ →
 ∀ ctx (inputs : List.Vector (Term ctx) m) (fuel : Term ctx),
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 let J := tags I.previous
 let index : Term ctx := Term.numeral (Encodable.encode c)
 Nonempty (Derivation U (orderGuard (Term.numeral bound) fuel)) →
 Nonempty (Derivation U (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
  (calculation J target inputs) (code producerTag target inputs)))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.InductionInterface
