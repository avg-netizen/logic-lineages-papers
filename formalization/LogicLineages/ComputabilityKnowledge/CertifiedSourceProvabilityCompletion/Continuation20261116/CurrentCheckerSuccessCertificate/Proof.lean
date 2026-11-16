module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCheckerSuccessCertificate.BridgeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCheckerSuccessCertificate.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence SixSol20261112.Fuel NamedArithmeticGraph
theorem oneCheckerSource : Targets.OneCheckerSource := by
 intro f lhs rhs k t ht
 dsimp only
 let Q : Program 1 → Program 1 → Program 3 → Program 5 :=
  fun old a baseX => CumulativePropositionalSource.verifier f lhs rhs old a baseX
 obtain ⟨old,a,baseX,offset,pF,pR,c,tagCK,pCK,tagG,pG,mtag,xtag,btag,etag,inventoryTag,evaluatorTag,producerTag,I,hK,hS,hcore,hiter,hold,ha,hbase,hb,hm,hret,hpackages,hCompiler,hEquality,hFull,hRetention,hPrior,h13,h12,hProp,hSeed,hSpecial,hTrace,hCompTrace,hComp,hBaseTrace,hBase,he,hInventory,hEvaluator,hProducer,hAll⟩ :=
  CurrentStructuralProducerSource.StatementChecks.exactSource f lhs rhs k t ht 5 Q
 have hA : Actual pF pR (CumulativePropositionalSource.verifier f lhs rhs old a baseX) c := hret.2.2.2.2.2.2.2.2.1
 have hchecker := GorbowNamedInternalProvability.Proof.exactCheckerTag 5 pF pR (Q old a baseX)
 have hbridge := BridgeProof.bridge f lhs rhs t old a baseX pF pR c hA hbase I inventoryTag producerTag hInventory hProducer
 exact ⟨old,a,baseX,offset,pF,pR,c,tagCK,pCK,tagG,pG,mtag,xtag,btag,etag,inventoryTag,evaluatorTag,producerTag,I,hK,hS,hcore,hiter,hold,ha,hbase,hb,hm,hret,hpackages,hCompiler,hEquality,hFull,hRetention,hPrior,h13,h12,hProp,hSeed,hSpecial,hTrace,hCompTrace,hComp,hBaseTrace,hBase,he,hInventory,hEvaluator,hProducer,hAll,hchecker,hbridge⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCheckerSuccessCertificate.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCheckerSuccessCertificate.Proof
