module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.GraphCalls
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.FourSyntaxProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.SeedGraph
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.RootGraph
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof FixedFormulaSubstitution
open CurrentRecursionBaseProgram.GraphPrimitives

def seedTags (K : PrescribedRuntimeCallCongruence.Tags) (pairTag rule13Tag : Nat) : CurrentRecursionBaseProgram.Tags :=
 ⟨pairTag,K.ctag,K.atag,K.numeralTag,K.mtag,K.constructorTag,rule13Tag,0,0⟩
def rawTagsValue {ctx : Nat} (tag offset : Nat) : List.Vector (Term ctx) 4 :=
 (SyntaxProof.addresses tag offset).map (fun t => Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode t)))
def rawRootValue {ctx : Nat} (K : Tags) (tag offset : Nat) (value : Term ctx) :=
 LiteralNumeralPrefix.numeralCall K.numeralTag value ::ᵥ rawTagsValue tag offset

def rootValue {ctx : Nat} (K : Tags) (pairTag rule13Tag tag offset : Nat) (value : Term ctx) :=
 let rv := rawTagsValue (ctx := ctx) tag offset
 let fq := formulaValue K.ctag K.atag (rawRootValue K tag offset value) rootTemplate (PrescribedRuntimeSpecialization.runtimeEnvironment 5)
 let fm := formulaValue K.ctag K.atag rv rootTemplate (PrescribedRuntimeSpecialization.headEnvironment 4)
 let fa := formulaValue K.ctag K.atag rv (.all rootTemplate) (PrescribedRuntimeSpecialization.runtimeEnvironment 4)
 LiteralMPRun.certificate K.mtag .zero fq
  (UniformClosedRule13Certificate.certificate K.ctag rule13Tag fm (LiteralNumeralPrefix.numeralCall K.numeralTag value))
  (CurrentRecursionBaseProgram.axiomValue (seedTags K pairTag rule13Tag) fa)

theorem rootGraph {arity ctx : Nat} (p : Program arity) (K : Tags) (H : CurrentCallCongruenceProgram.Installation p K)
 (pairTag rule13Tag : Nat)
 (hp : (nodes p)[pairTag]? = some ⟨2,HistoryCodec.pair⟩)
 (h13 : (nodes p)[rule13Tag]? = some ⟨2,UniformClosedRule13.lineConstructor⟩)
 (tag offset : Nat) (value : Term ctx) :
 Computes p rootSeed (GraphValues.args tag offset value) (rootValue K pairTag rule13Tag tag offset value) := by
 let J := seedTags K pairTag rule13Tag
 have HJ : CurrentCompositionProducerProgram.SeedGraph.SeedNodes p J := ⟨hp,H.hc,H.ha,H.hm,h13⟩
 have ht : ∀ i, Computes p (rawTags.get i) (GraphValues.args tag offset value) ((rawTagsValue tag offset).get i) := by
  intro i
  simpa only [rawTagsValue,List.Vector.get_map] using GraphValues.tagsGraph p K H tag offset value i
 have hr : ∀ i, Computes p (rawRoot.get i) (GraphValues.args tag offset value) ((rawRootValue K tag offset value).get i) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact GraphValues.inputGraph p K H tag offset value
  · exact ht j
 have hq := quoteGraph p (GraphValues.args tag offset value) rootTemplate (PrescribedRuntimeSpecialization.runtimeEnvironment 5) rawRoot.get (rawRootValue K tag offset value) K.ctag K.atag H.hc H.ha hr
 have hm := headGraph p (GraphValues.args tag offset value) rootTemplate rawTags.get (rawTagsValue tag offset) K.ctag K.atag H.hc H.ha ht
 have ha := quoteGraph p (GraphValues.args tag offset value) (.all rootTemplate) (PrescribedRuntimeSpecialization.runtimeEnvironment 4) rawTags.get (rawTagsValue tag offset) K.ctag K.atag H.hc H.ha ht
 have hax := CurrentCompositionProducerProgram.SeedGraph.axiomGraph p _ J HJ _ _ ha
 exact mpGraph p _ K.mtag H.hm _ _ _ _ _ _ hq
  (allGraph p _ K.ctag rule13Tag H.hc h13 _ _ _ _ hm (GraphValues.inputGraph p K H tag offset value)) hax

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.RootGraph
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.RootGraph
