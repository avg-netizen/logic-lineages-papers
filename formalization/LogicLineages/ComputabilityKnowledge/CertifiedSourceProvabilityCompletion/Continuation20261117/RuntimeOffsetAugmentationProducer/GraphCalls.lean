module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.GraphValues
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.GraphCalls
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof

def nums {ctx : Nat} (K : Tags) (value : Term ctx) : List.Vector (Term ctx) 1 := LiteralNumeralPrefix.numeralCall K.numeralTag value ::ᵥ nil
def calls {ctx : Nat} (K : Tags) (tag offset : Nat) (value : Term ctx) : List.Vector (Term ctx) 2 :=
 callValue K (Term.numeral (tag+2)) (nums K value) ::ᵥ callValue K (Term.numeral (tag+offset)) (nums K value) ::ᵥ nil

theorem left {arity ctx : Nat} (p : Program arity) (K : Tags) (H : CurrentCallCongruenceProgram.Installation p K)
 (tag offset : Nat) (value : Term ctx) : Computes p leftCode (GraphValues.args tag offset value)
  (callValue K (Term.numeral tag) (nums K value)) := by
 apply CurrentCompositionProducerProgram.CallEncoding.graph p _ K H target (rawInput ::ᵥ nil) (Term.numeral tag) (nums K value)
 · exact GraphValues.targetGraph p tag offset value
 · intro i
   have hi : i = 0 := Fin.eq_zero i
   subst i
   exact GraphValues.inputGraph p K H tag offset value

theorem first {arity ctx : Nat} (p : Program arity) (K : Tags) (H : CurrentCallCongruenceProgram.Installation p K)
 (tag offset : Nat) (value : Term ctx) : Computes p firstCall (GraphValues.args tag offset value)
  (callValue K (Term.numeral (tag+2)) (nums K value)) := by
 apply CurrentCompositionProducerProgram.CallEncoding.graph p _ K H firstTag (rawInput ::ᵥ nil) (Term.numeral (tag+2)) (nums K value)
 · exact GraphValues.firstGraph p tag offset value
 · intro i
   have hi : i = 0 := Fin.eq_zero i
   subst i
   exact GraphValues.inputGraph p K H tag offset value

theorem second {arity ctx : Nat} (p : Program arity) (K : Tags) (H : CurrentCallCongruenceProgram.Installation p K)
 (tag offset : Nat) (value : Term ctx) : Computes p secondCall (GraphValues.args tag offset value)
  (callValue K (Term.numeral (tag+offset)) (nums K value)) := by
 apply CurrentCompositionProducerProgram.CallEncoding.graph p _ K H secondTag (rawInput ::ᵥ nil) (Term.numeral (tag+offset)) (nums K value)
 · exact GraphValues.secondGraph p tag offset value
 · intro i
   have hi : i = 0 := Fin.eq_zero i
   subst i
   exact GraphValues.inputGraph p K H tag offset value

theorem middle {arity ctx : Nat} (p : Program arity) (K : Tags) (H : CurrentCallCongruenceProgram.Installation p K)
 (tag offset : Nat) (value : Term ctx) : Computes p middleCode (GraphValues.args tag offset value)
  (callValue K (Term.numeral (tag+1)) (calls K tag offset value)) := by
 apply CurrentCompositionProducerProgram.CallEncoding.graph p _ K H projectionTag (firstCall ::ᵥ secondCall ::ᵥ nil) _ (calls K tag offset value)
 · exact GraphValues.projectionGraph p tag offset value
 · intro i
   refine Fin.cases ?_ (fun j => ?_) i
   · exact first p K H tag offset value
   · have hj : j = 0 := Fin.eq_zero j
     subst j
     exact second p K H tag offset value

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.GraphCalls
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.GraphCalls
