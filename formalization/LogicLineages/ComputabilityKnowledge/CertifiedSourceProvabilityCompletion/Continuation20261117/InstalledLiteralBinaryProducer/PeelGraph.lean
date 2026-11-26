module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.GraphSupport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.PeelGraph
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence



open HistoryRuleSuffix

open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof

theorem peelGraph {arity ctx : Nat} (root : Program arity) (peelTag : Nat)
 (hp : (nodes root)[peelTag]? = some ⟨3,RuntimeOffsetAugmentationProducer.program⟩)
 (a b c tag offset : Nat) (i : Fin 5) (r s : Term ctx)
 (hi : (GraphSupport.args a b c r s).get i = Term.numeral offset) :
 Computes root (peel tag i) (GraphSupport.args a b c r s)
  (call peelTag (Term.numeral tag ::ᵥ Term.numeral offset ::ᵥ GorbowRegistryTuple.headerTerm 2 0 [r,s] ::ᵥ nil)) := by
 apply CurrentRecursionAccumulator.GraphSupport.composition root _ _ peelTag hp _
  (Term.numeral tag ::ᵥ Term.numeral offset ::ᵥ GorbowRegistryTuple.headerTerm 2 0 [r,s] ::ᵥ nil)
 intro j
 refine Fin.cases ?_ (fun j => ?_) j
 · exact constantValue root _ tag
 · refine Fin.cases ?_ (fun j => ?_) j
   · rw [← hi]
     exact projection root _ i
   · have hj : j = 0 := Fin.eq_zero j
     subst j
     exact GraphSupport.header root a b c r s

theorem graph {arity ctx : Nat} (root : Program arity) (K : PrescribedRuntimeCallCongruence.Tags)
 (H : CurrentCallCongruenceProgram.Installation root K) (pF0 : Program 1) (pCK : Program 2)
 (box : Program 6) (outer : Program 5) (peelTag : Nat)
 (hp : (nodes root)[peelTag]? = some ⟨3,RuntimeOffsetAugmentationProducer.program⟩) (r s : Term ctx) :
 Computes root peelCertificate (inputs pF0 pCK box outer r s)
  (RetainedBaseSourceCalculation.peelCertificate K pF0 pCK box outer peelTag (GorbowRegistryTuple.headerTerm 2 0 [r,s])) := by
 let inner := GorbowNamedInternalProvability.augment pF0 pCK
 let pF := GorbowNamedInternalProvability.augment inner box
 let a := secondOffset pF outer
 let b := secondOffset inner box
 let c := secondOffset pF0 pCK
 have h68 := peelGraph root peelTag hp a b c 6 a 0 r s rfl
 have h810 := peelGraph root peelTag hp a b c 8 b 1 r s rfl
 have h1012 := peelGraph root peelTag hp a b c 10 c 2 r s rfl
 have h610 := CurrentCallCongruenceProgram.TransitivityGraph.transitivityGraph root (GraphSupport.args a b c r s) K H
  (rawCall 6) (rawCall 8) (rawCall 10) (peel 6 0) (peel 8 1) _ _ _ _ _
  (GraphSupport.call root K H a b c 6 r s) (GraphSupport.call root K H a b c 8 r s)
  (GraphSupport.call root K H a b c 10 r s) h68 h810
 exact CurrentCallCongruenceProgram.TransitivityGraph.transitivityGraph root (GraphSupport.args a b c r s) K H
  (rawCall 6) (rawCall 10) (rawCall 12) _ (peel 10 2) _ _ _ _ _
  (GraphSupport.call root K H a b c 6 r s) (GraphSupport.call root K H a b c 10 r s)
  (GraphSupport.call root K H a b c 12 r s) h610 h1012

theorem calculationGraph {arity ctx : Nat} (root : Program arity) (K : PrescribedRuntimeCallCongruence.Tags)
 (H : CurrentCallCongruenceProgram.Installation root K) (pF0 : Program 1) (pCK : Program 2)
 (box : Program 6) (outer : Program 5) (peelTag baseTag : Nat)
 (hp : (nodes root)[peelTag]? = some ⟨3,RuntimeOffsetAugmentationProducer.program⟩)
 (hb : (nodes root)[12]? = some ⟨1,pF0⟩)
 (hbase : (nodes root)[baseTag]? = some ⟨2,CurrentStructuralProducerCompiler.compile pF0⟩)
 (r s : Term ctx) :
 Computes root (calculation pF0) (inputs pF0 pCK box outer r s)
  (RetainedBaseSourceCalculation.certificate K pF0 pCK box outer peelTag baseTag (GorbowRegistryTuple.headerTerm 2 0 [r,s])) := by
 let inner := GorbowNamedInternalProvability.augment pF0 pCK
 let pF := GorbowNamedInternalProvability.augment inner box
 let a := secondOffset pF outer
 let b := secondOffset inner box
 let c := secondOffset pF0 pCK
 exact CurrentCallCongruenceProgram.TransitivityGraph.transitivityGraph root (GraphSupport.args a b c r s) K H
  (rawCall 6) (rawCall 12) (output pF0) peelCertificate (baseCertificate pF0) _ _ _ _ _
  (GraphSupport.call root K H a b c 6 r s) (GraphSupport.call root K H a b c 12 r s)
  (GraphSupport.outputGraph root K H pF0 hb a b c r s) (graph root K H pF0 pCK box outer peelTag hp r s)
  (GraphSupport.baseGraph root pF0 baseTag hbase a b c r s)

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.PeelGraph
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.PeelGraph
