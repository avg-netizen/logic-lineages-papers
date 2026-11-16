module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram.SwapGraph
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram.JoinGraph
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof
theorem joinCall {arity m ctx : Nat} (p : Program arity) (f : Program m) (g : Program (m+2))
 (B : Program (m+1)) (G : Program (m+3)) (N : GraphNodes p f g B G)
 (counter previous target : Term ctx) (inputs : List.Vector (Term ctx) m) :
 Computes p (CurrentRecursionAccumulator.join (formula f g) (step f g G))
  (counter ::ᵥ previous ::ᵥ target ::ᵥ inputs)
  (LiteralMPRun.certificate N.mpTag .zero
   (call N.formulaTag (target ::ᵥ .succ counter ::ᵥ inputs))
   (call N.stepTag (target ::ᵥ counter ::ᵥ inputs)) previous) := by
 apply CurrentRecursionAccumulator.GraphSupport.composition p _ LiteralRawMP.constructor N.mpTag N.hmp _
  (.zero ::ᵥ call N.formulaTag (target ::ᵥ .succ counter ::ᵥ inputs) ::ᵥ
   call N.stepTag (target ::ᵥ counter ::ᵥ inputs) ::ᵥ previous ::ᵥ nil)
 intro i
 cases i using Fin.cases with
 | zero => exact constantValue p _ 0
 | succ i => cases i using Fin.cases with
   | zero => exact SwapGraph.atSuccessor p _ N.formulaTag N.hformula counter previous target inputs
   | succ i => cases i using Fin.cases with
     | zero => exact SwapGraph.atCounter p _ N.stepTag N.hstep counter previous target inputs
     | succ i => cases i using Fin.cases with
       | zero => exact projection p _ 1
       | succ i => exact Fin.elim0 i

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram.JoinGraph
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerProgram.JoinGraph
