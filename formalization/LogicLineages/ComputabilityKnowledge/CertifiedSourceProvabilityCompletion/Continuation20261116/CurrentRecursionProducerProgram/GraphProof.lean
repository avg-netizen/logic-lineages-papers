module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram.AccumulatorGraph
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram.GraphProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof
theorem exactGraph : Targets.InternalGraph := by
 intro arity p m f g B G N ctx target counter inputs
 obtain ⟨hz⟩ := AccumulatorGraph.zero p f g B G N target inputs
 obtain ⟨hs⟩ := AccumulatorGraph.successor p f g B G N target counter inputs
 obtain ⟨hwz⟩ := SwapGraph.swapCall p (accumulator f g B G) N.accumulatorTag N.haccumulator target .zero inputs N.publicTag N.hpublic
 obtain ⟨hws⟩ := SwapGraph.swapCall p (accumulator f g B G) N.accumulatorTag N.haccumulator target (.succ counter) inputs N.publicTag N.hpublic
 obtain ⟨hwp⟩ := SwapGraph.swapCall p (accumulator f g B G) N.accumulatorTag N.haccumulator target counter inputs N.publicTag N.hpublic
 have hprev := Support.equalitySymmetry _ _ hwp
 have hmp := Logic.callCongruence (GorbowPRNumeralCalculation.Theory p) N.mpTag
  ((.zero : Term ctx) ::ᵥ call N.formulaTag (target ::ᵥ .succ counter ::ᵥ inputs) ::ᵥ
   call N.stepTag (target ::ᵥ counter ::ᵥ inputs) ::ᵥ call N.accumulatorTag (counter ::ᵥ target ::ᵥ inputs) ::ᵥ nil)
  ((.zero : Term ctx) ::ᵥ call N.formulaTag (target ::ᵥ .succ counter ::ᵥ inputs) ::ᵥ
   call N.stepTag (target ::ᵥ counter ::ᵥ inputs) ::ᵥ call N.publicTag (target ::ᵥ counter ::ᵥ inputs) ::ᵥ nil)
  (fun i => by
   cases i using Fin.cases with
   | zero => exact .logical (.reflexive _)
   | succ i => cases i using Fin.cases with
     | zero => exact .logical (.reflexive _)
     | succ i => cases i using Fin.cases with
       | zero => exact .logical (.reflexive _)
       | succ i => cases i using Fin.cases with
         | zero => exact hprev
         | succ i => exact Fin.elim0 i)
 exact ⟨.mp (.mp (.logical (.andIntro _ _)) (Logic.trans _ _ _ hwz hz))
  (Logic.trans _ _ _ hws (Logic.trans _ _ _ hs hmp))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram.GraphProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram.GraphProof
