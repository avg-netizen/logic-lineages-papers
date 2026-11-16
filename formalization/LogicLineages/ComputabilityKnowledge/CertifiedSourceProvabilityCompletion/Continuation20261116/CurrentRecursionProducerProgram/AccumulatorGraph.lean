module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram.JoinGraph
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram.AccumulatorGraph
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof
theorem zero {arity m ctx : Nat} (p : Program arity) (f : Program m) (g : Program (m+2))
 (B : Program (m+1)) (G : Program (m+3)) (N : GraphNodes p f g B G)
 (target : Term ctx) (inputs : List.Vector (Term ctx) m) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (call N.accumulatorTag (.zero ::ᵥ target ::ᵥ inputs)) (call N.baseTag (target ::ᵥ inputs)))) := by
 let b := CurrentRecursionBaseProgram.program f B
 let j := CurrentRecursionAccumulator.join (formula f g) (step f g G)
 have hb := GorbowPRSubtree.Proof.lookupTransport arity p N.accumulatorTag ⟨m+2,accumulator f g B G⟩ 1 ⟨m+1,b⟩ N.haccumulator
  (GorbowPRChildTags.Proof.recursionBase (m+1) b j)
 obtain ⟨hz⟩ := GorbowPRSymbolicEquations.Proof.recursionZeroEquation arity p N.accumulatorTag (m+1) b j N.haccumulator ctx (target ::ᵥ inputs)
 obtain ⟨hc⟩ := GorbowPRInternalCoherence.Proof.registryCoherence arity p (N.accumulatorTag+1) N.baseTag (m+1) b hb N.hbase ctx (target ::ᵥ inputs)
 exact ⟨Logic.trans _ _ _ hz hc⟩

theorem successor {arity m ctx : Nat} (p : Program arity) (f : Program m) (g : Program (m+2))
 (B : Program (m+1)) (G : Program (m+3)) (N : GraphNodes p f g B G)
 (target counter : Term ctx) (inputs : List.Vector (Term ctx) m) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (call N.accumulatorTag (.succ counter ::ᵥ target ::ᵥ inputs))
   (LiteralMPRun.certificate N.mpTag .zero
    (call N.formulaTag (target ::ᵥ .succ counter ::ᵥ inputs))
    (call N.stepTag (target ::ᵥ counter ::ᵥ inputs))
    (call N.accumulatorTag (counter ::ᵥ target ::ᵥ inputs))))) := by
 let b := CurrentRecursionBaseProgram.program f B
 let j := CurrentRecursionAccumulator.join (formula f g) (step f g G)
 obtain ⟨hr⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation arity p N.accumulatorTag (m+1) b j
  N.haccumulator ctx counter (target ::ᵥ inputs)
 obtain ⟨hj⟩ := JoinGraph.joinCall p f g B G N counter (call N.accumulatorTag (counter ::ᵥ target ::ᵥ inputs)) target inputs
  (N.accumulatorTag+GorbowPRChildTags.stepTag b)
  (Equations.recursionStepChild p N.accumulatorTag b j N.haccumulator)
 exact ⟨Logic.trans _ _ _ hr hj⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram.AccumulatorGraph
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram.AccumulatorGraph
