module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationProducer.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralTemplateQuote.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations List.Vector SixSol20261113 HistoryRuleSuffix
/-- Original term syntax, explicitly restricted to the arithmetic fragment.
Universal-function/program-node quotation is a separate unpaid obligation. -/
def Arithmetic {k : Nat} : Term k → Prop
 | .var _ => True
 | .zero => True
 | .succ t => Arithmetic t
 | .add t u => Arithmetic t ∧ Arithmetic u
 | .mul t u => Arithmetic t ∧ Arithmetic u
 | .universalFunction _ => False
/-- Fixed-template value compiler, not a uniform evaluator of program codes. -/
def valueProgram {k : Nat} : Term k → Program k
 | .var i => .projection i
 | .zero => constant k 0
 | .succ t => applyOne .succ (valueProgram t)
 | .add t u => applyTwo HistoryCodec.add (valueProgram u) (valueProgram t)
 | .mul t u => applyTwo HistoryCodec.multiply (valueProgram u) (valueProgram t)
 | .universalFunction _ => constant k 0
/-- Structural compilation into literal original certificate constructors.
The universalFunction fallback carries NO correctness claim. -/
def certificateProgram {k : Nat} : Term k → Program k
 | .var i => RawAdditionIteration.singleton (applyOne RawReflexivity.lineConstructor
   (LiteralTemplateQuote.templateQuote (.var i)))
 | .zero => RawAdditionIteration.singleton (applyOne RawReflexivity.lineConstructor
   (LiteralTemplateQuote.templateQuote (.zero : Term k)))
 | .succ t => .composition RawSuccessorProducer.producer
   (Fin.cases (LiteralTemplateQuote.templateQuote t)
    (Fin.cases (valueProgram t) (Fin.cases (certificateProgram t) Fin.elim0)))
 | .add t u => .composition RawAdditionProducer.producer
   (Fin.cases (LiteralTemplateQuote.templateQuote t)
    (Fin.cases (LiteralTemplateQuote.templateQuote u)
     (Fin.cases (valueProgram t) (Fin.cases (valueProgram u)
      (Fin.cases (certificateProgram t) (Fin.cases (certificateProgram u) Fin.elim0))))))
 | .mul t u => .composition RawMultiplicationProducer.producer
   (Fin.cases (LiteralTemplateQuote.templateQuote t)
    (Fin.cases (LiteralTemplateQuote.templateQuote u)
     (Fin.cases (valueProgram t) (Fin.cases (valueProgram u)
      (Fin.cases (certificateProgram t) (Fin.cases (certificateProgram u) Fin.elim0))))))
 | .universalFunction _ => constant k 0
structure Installation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3) extends
 toProducers : RawMultiplicationProducer.Installation p old a x where
 successorProducerTag : Nat
 hsuccessorProducer : (nodes p)[successorProducerTag]? = some ⟨3,RawSuccessorProducer.producer⟩
/-- Only literal registry memberships; no semantic evaluation or success fields. -/
structure TemplateInstallation {n k : Nat} (p : Program n) (t : Term k) where
 quoteTag : Nat
 valueTag : Nat
 certificateTag : Nat
 hquote : (nodes p)[quoteTag]? = some ⟨k,LiteralTemplateQuote.templateQuote t⟩
 hvalue : (nodes p)[valueTag]? = some ⟨k,valueProgram t⟩
 hcertificate : (nodes p)[certificateTag]? = some ⟨k,certificateProgram t⟩
def instantiatedValue {k ctx : Nat} (t : Term k) (values : List.Vector (Term ctx) k) : Term ctx :=
 GorbowSubstitution.substitute (fun i => values.get i) t
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation
