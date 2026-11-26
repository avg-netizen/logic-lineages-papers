module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.HeaderGraph
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.PeelGraph
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.BoxNodes
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.GraphProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence



open HistoryRuleSuffix

open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof

theorem exactGraph : Targets.Graph := by
 intro f lhs rhs old a baseX pF0 pR pCK pG
 dsimp only
 intro I peelTag baseProducerTag producerTag hpeel hbase hproducer ctx r s
 let t := CurrentNamedHeaderCertificate.template
 let box := InstalledProducerExtra.container pG (extra f lhs rhs old a baseX pF0)
 let pF := selected f lhs rhs old a baseX pF0 pCK pG
 let outer := CumulativePropositionalSource.verifier f lhs rhs old a baseX
 let root := CumulativePropositionalSource.root f lhs rhs pF pR old a baseX
 let R := CurrentPublishedProvabilityIntroduction.RuntimeRebase.shared root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I
 let K := tags R.previous
 let J := R.previous.previous.previous.previous.template
 have H : CurrentCallCongruenceProgram.Installation root K :=
  ⟨R.previous.current.h_ctag,R.previous.current.h_atag,R.previous.previous.previous.previous.previous.hnumeral,
   R.previous.previous.previous.previous.previous.hmp,R.previous.current.h_constructor,
   R.previous.previous.previous.previous.previous.hc,R.previous.previous.previous.previous.previous.hreflexivity⟩
 obtain ⟨h6,h8,h10,h12⟩ := BoxNodes.nodes f lhs rhs t old a baseX pF0 pR pCK box
 let inner := GorbowNamedInternalProvability.augment pF0 pCK
 let oa := secondOffset pF outer
 let ob := secondOffset inner box
 let oc := secondOffset pF0 pCK
 let v := GorbowRegistryTuple.headerTerm 2 0 [r,s]
 have hout : Computes root (output pF0) (GraphSupport.args oa ob oc r s)
  (LiteralNumeralPrefix.numeralCall K.numeralTag (call 6 (v ::ᵥ nil))) := by
  intro tag ht
  obtain ⟨hc⟩ := GraphSupport.outputGraph root K H pF0 h12 oa ob oc r s tag ht
  obtain ⟨h68⟩ := RetainedBaseSourceCalculation.SymbolicProof.peel root 6 pF outer h6 v
  obtain ⟨h810⟩ := RetainedBaseSourceCalculation.SymbolicProof.peel root 8 inner box h8 v
  obtain ⟨h1012⟩ := RetainedBaseSourceCalculation.SymbolicProof.peel root 10 pF0 pCK h10 v
  have he := Logic.trans _ _ _ h68 (Logic.trans _ _ _ h810 h1012)
  have hn := HistoryLookup.DestructorProof.unaryCallCongruence K.numeralTag _ _ (Support.equalitySymmetry _ _ he)
  exact ⟨Logic.trans _ _ _ hc hn⟩
 have hg := CurrentCallCongruenceProgram.TransitivityGraph.transitivityGraph root (GraphSupport.args oa ob oc r s) K H
  (.composition CurrentNamedHeaderTransport.leftQuote pairInputs) (rawCall 6) (output pF0)
  (.composition CurrentNamedHeaderTransport.program pairInputs) (calculation pF0) _ _ _ _ _
  (HeaderGraph.left root K H oa ob oc r s) (GraphSupport.call root K H oa ob oc 6 r s) hout
  (HeaderGraph.lifted root K H R.currentK.ptag R.previous.previous.current.constructorTag J.certificateTag
   R.currentK.h_ptag R.previous.previous.current.h_constructor J.hcertificate oa ob oc r s)
  (PeelGraph.calculationGraph root K H pF0 pCK box outer peelTag baseProducerTag hpeel h12 hbase r s)
 exact hg producerTag hproducer

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.GraphProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.GraphProof
