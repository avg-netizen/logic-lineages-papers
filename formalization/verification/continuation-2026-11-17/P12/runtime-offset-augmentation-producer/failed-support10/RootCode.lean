module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.RootGraph
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.RootCode
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph FixedFormulaSubstitution
open CurrentRecursionProducerCore

theorem rootCode {arity ctx : Nat} (p : Program arity) (K : Tags) (H : CurrentCallCongruenceProgram.Installation p K)
 (pairTag rule13Tag : Nat)
 (hp : (nodes p)[pairTag]? = some ⟨2,HistoryCodec.pair⟩)
 (h13 : (nodes p)[rule13Tag]? = some ⟨2,UniformClosedRule13.lineConstructor⟩)
 (tag offset : Nat) (value : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (RootGraph.rootValue K pairTag rule13Tag tag offset value)
   (PrescribedSourceAxiomSpecialization.certificate K.mtag K.ctag K.atag rule13Tag
    (SyntaxProof.rootAt tag offset) (LiteralNumeralPrefix.numeralCall K.numeralTag value ::ᵥ nil)))) := by
 let J := RootGraph.seedTags K pairTag rule13Tag
 let a : Term ctx := rawNumeral (Term.numeral tag)
 let b : Term ctx := rawNumeral (Term.numeral (tag+1))
 let c : Term ctx := rawNumeral (Term.numeral (tag+2))
 let d : Term ctx := rawNumeral (Term.numeral (tag+offset))
 let v := LiteralNumeralPrefix.numeralCall K.numeralTag value
 have htags : FourPlugProof.appended nil a b c d = RootGraph.rawTagsValue tag offset := by
  rw [FourSyntaxProof.rawFour]
  rfl
 have hroot : FourPlugProof.appended (v ::ᵥ nil) a b c d = RootGraph.rawRootValue K tag offset value := by
  rw [FourSyntaxProof.rawFive]
  rfl
 obtain ⟨hf⟩ := FourPlugProof.formula p K.ctag K.atag H.hc H.ha (v ::ᵥ nil) a b c d tag (tag+1) (tag+2) (tag+offset)
  (.logical (.reflexive _)) (.logical (.reflexive _)) (.logical (.reflexive _)) (.logical (.reflexive _)) rootTemplate
 rw [hroot,FourSyntaxProof.root] at hf
 obtain ⟨hm⟩ := FourPlugProof.head p K.ctag K.atag H.hc H.ha nil a b c d tag (tag+1) (tag+2) (tag+offset)
  (.logical (.reflexive _)) (.logical (.reflexive _)) (.logical (.reflexive _)) (.logical (.reflexive _)) rootTemplate
 rw [htags,FourSyntaxProof.root] at hm
 obtain ⟨ha⟩ := FourPlugProof.formula p K.ctag K.atag H.hc H.ha nil a b c d tag (tag+1) (tag+2) (tag+offset)
  (.logical (.reflexive _)) (.logical (.reflexive _)) (.logical (.reflexive _)) (.logical (.reflexive _)) (.all rootTemplate)
 rw [htags,FourSyntaxProof.allRoot] at ha
 obtain ⟨hclosed⟩ := SeedTag.closedFormula (ctx := ctx) p K.ctag K.atag H.hc H.ha (.all (SyntaxProof.rootAt tag offset))
 obtain ⟨hax⟩ := AxiomTrace.axiomCode p J hp H.hc _ _ (Logic.trans _ _ _ ha hclosed)
 obtain ⟨hline⟩ := CallTransport.rule13 p K.ctag rule13Tag K.ctag rule13Tag H.hc h13 H.hc h13 _ _ v v hm (.logical (.reflexive _))
 obtain ⟨hmp⟩ := CallTransport.mp p K.mtag K.mtag H.hm H.hm _ _ _ _ _ _ hf hline hax
 simpa only [RootGraph.rootValue,PrescribedSourceAxiomSpecialization.certificate,PrescribedRuntimeSpecialization.certificate,
  UniformRuntimeSpecializationStep.certificate,PrescribedRuntimeSpecialization.EnvironmentProof.stepValue,
  PrescribedRuntimeSpecialization.value,List.Vector.tail_cons,List.Vector.head_cons,
  PrescribedSourceAxiomSpecialization.seed,GorbowStandardInduction.universalClosure] using (show Nonempty _ from ⟨hmp⟩)

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.RootCode
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.RootCode
