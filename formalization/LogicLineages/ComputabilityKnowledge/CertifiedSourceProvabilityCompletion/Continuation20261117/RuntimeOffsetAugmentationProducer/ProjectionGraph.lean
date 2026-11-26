module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.RootGraph
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.ProjectionGraph
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof FixedFormulaSubstitution
open CurrentRecursionProducerCore

theorem projectionGraph {arity ctx : Nat} (p : Program arity) (K : Tags) (H : CurrentCallCongruenceProgram.Installation p K)
 (pairTag rule13Tag : Nat)
 (hp : (nodes p)[pairTag]? = some ⟨2,HistoryCodec.pair⟩)
 (h13 : (nodes p)[rule13Tag]? = some ⟨2,UniformClosedRule13.lineConstructor⟩)
 (tag offset : Nat) (value : Term ctx) :
 Computes p projectionSeed (GraphValues.args tag offset value)
  (PrescribedSourceAxiomSpecialization.certificate K.mtag K.ctag K.atag rule13Tag
   (CorrectedAugmentationErasure.projectionFormula tag) (GraphCalls.calls K tag offset value)) := by
 let J := RootGraph.seedTags K pairTag rule13Tag
 have HJ : CurrentCompositionProducerProgram.SeedGraph.SeedNodes p J := ⟨hp,H.hc,H.ha,H.hm,h13⟩
 let xs := GraphCalls.calls K tag offset value
 let tagCode : Term ctx := rawNumeral (Term.numeral (tag+1))
 let rv := xs.head ::ᵥ xs.tail.head ::ᵥ tagCode ::ᵥ nil
 have hraw : ∀ i, Computes p ((firstCall ::ᵥ secondCall ::ᵥ applyOne LiteralNumeralPrefix.numeralCode projectionTag ::ᵥ nil).get i)
  (GraphValues.args tag offset value) (rv.get i) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact GraphCalls.first p K H tag offset value
  · refine Fin.cases ?_ (fun l => ?_) j
    · exact GraphCalls.second p K H tag offset value
    · have hl : l = 0 := Fin.eq_zero l
      subst l
      exact GraphValues.quoteTag p K H tag offset (tag+1) value projectionTag (GraphValues.projectionGraph p tag offset value)
 have hg := CurrentCompositionProducerProgram.SeedGraph.seedGraph p (GraphValues.args tag offset value) J HJ 2 projectionTemplate _ rv hraw
 have heq : TagPlug.appendRaw xs tagCode = rv := by
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun l => ?_) j
    · rfl
    · have hl : l = 0 := Fin.eq_zero l
      subst l
      rfl
 obtain ⟨he⟩ := SeedTag.seed p J hp H.hc H.ha H.hm h13 tagCode (tag+1) (.logical (.reflexive _)) 2 projectionTemplate xs
 rw [heq,SyntaxProof.projection] at he
 intro addr ht
 obtain ⟨hcomp⟩ := hg addr ht
 exact ⟨Logic.trans _ _ _ hcomp he⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.ProjectionGraph
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.ProjectionGraph
