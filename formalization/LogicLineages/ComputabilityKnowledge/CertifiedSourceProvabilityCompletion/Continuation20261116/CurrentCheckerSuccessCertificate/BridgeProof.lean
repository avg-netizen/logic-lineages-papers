module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCheckerSuccessCertificate.LocalQuotation
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCheckerSuccessCertificate.BridgeProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence SixSol20261112.Fuel NamedArithmeticGraph
theorem bridge (installed : Formula 1) (lhs rhs : Term 1) {k : Nat} (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code)
 (hA : Actual pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX) c)
 (hn : ∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v)
 (I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX))
 (inventoryTag producerTag : Nat)
 (hInventory : (nodes (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX))[inventoryTag]? =
  some ⟨6,CurrentStructuralProducerInventory.carrier installed lhs rhs t old a baseX
   (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)⟩)
 (hProducer : (nodes (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX))[producerTag]? =
  some ⟨6,CurrentStructuralProducerCompiler.compile (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)⟩) :
 ∃ outerBound : Nat, ∀ ctx (innerFuel formula certificate : Term ctx),
 Nonempty (Derivation (S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX))
  (.imp (success pF c innerFuel formula certificate)
   (accepted I.currentK.coreTag I.currentK.verifierTag (Term.numeral (Encodable.encode c))
    (Term.numeral outerBound) (quotedSuccess (tags I.previous) pF c innerFuel formula certificate)
    (proofCode producerTag pF c innerFuel formula certificate)))) := by
 let q := CumulativePropositionalSource.verifier installed lhs rhs old a baseX
 let p := CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX
 let U := S pF pR q
 have hchecker := GorbowNamedInternalProvability.Proof.exactCheckerTag 5 pF pR q
 obtain ⟨bound,hcore⟩ := CurrentStructuralProducerCore.StatementChecks.exactSource installed lhs rhs k t old a baseX pF pR c hA hn I
 refine ⟨bound,?_⟩
 intro ctx innerFuel formula certificate
 let args := checkerInputs c innerFuel formula certificate
 have h := hcore 5 q inventoryTag hInventory 5 q (.here q rfl)
  (GorbowNamedInternalProvability.checkerTag pF) producerTag hchecker hProducer ctx args
  (Term.numeral bound) ⟨FuelWitness.ExtractionLogicProof.orderRefl _⟩
 obtain ⟨h⟩ := CurrentStructuralProducerCore.CoreTools.project U _ _ _ _ _ _ h
 obtain ⟨heq⟩ := LocalQuotation.resultOne U (tags I.previous) pF c innerFuel formula certificate
 obtain ⟨hc⟩ := PrescribedRuntimeSpecialization.BaseProof.coreTransport U
  [success pF c innerFuel formula certificate] I.currentK.coreTag
  (Term.numeral (Encodable.encode c)) (Term.numeral bound) _ _ _ heq (.base h)
 obtain ⟨ha⟩ := CurrentImplicationCertificate.AlgebraSupport.acceptedOfCore p installed lhs rhs t old a _ I U
  (CumulativePropositionalSource.SeedSourceProof.inclusion installed lhs rhs pF pR old a baseX)
  [success pF c innerFuel formula certificate] _ _ _ _ hc
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge ha)⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCheckerSuccessCertificate.BridgeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCheckerSuccessCertificate.BridgeProof
