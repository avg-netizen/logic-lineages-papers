module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.InductionInterface
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.LeafProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence SixSol20261112.Fuel NamedArithmeticGraph
theorem leaf (installed : Formula 1) (lhs rhs : Term 1) {k : Nat} (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code)
 (I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX))
 (lb cb rb : Nat)
 (hL : BoundInterfaces.Leaf installed lhs rhs t old a baseX pF pR c I lb)
 {n : Nat} (kind : CurrentBasicProducerProgram.Kind n) (J : CurrentBasicProducerProgram.Tags)
 (target producerTag : Nat)
 (hJ : CurrentBasicProducerProgram.Installation (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX) J)
 (hq : (nodes (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX))[target]? =
  some ⟨n,CurrentBasicProducerProgram.evaluator kind⟩)
 (hp : (nodes (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX))[producerTag]? =
  some ⟨n+1,CurrentBasicProducerProgram.program kind⟩)
 (ctx : Nat) (inputs : List.Vector (Term ctx) n) (fuel : Term ctx)
 (hg : Nonempty (Derivation (S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX))
  (orderGuard (Term.numeral (lb+cb+rb)) fuel))) :
 Nonempty (Derivation (S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX))
  (accepted I.currentK.coreTag I.currentK.verifierTag (Term.numeral (Encodable.encode c)) fuel
   (calculation (tags I.previous) target inputs) (code producerTag target inputs))) := by
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 obtain ⟨hguard⟩ := (GuardProof.lower U lb cb rb fuel hg).1
 obtain ⟨hc⟩ := hL n kind J target producerTag hJ hq hp ctx [] inputs fuel ⟨.base hguard⟩
 exact CoreTools.ofCore _ installed lhs rhs t old a _ I U
  (CumulativePropositionalSource.SeedSourceProof.inclusion installed lhs rhs pF pR old a baseX)
  _ _ _ _ ⟨Hilbert.Local.finish hc⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.LeafProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.LeafProof
