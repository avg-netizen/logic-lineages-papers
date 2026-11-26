module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerSource.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
/-- The original child calculation proposition, now at actual evaluator and
actual producer addresses in the same selected root. No success oracle. -/
def childFormula {ctx n : Nat} (J : PrescribedRuntimeCallCongruence.Tags) (evaluatorTag : Nat)
 (inputs : List.Vector (Term ctx) n) : Term ctx :=
 equalValue J.ctag J.atag
  (callValue J (Term.numeral evaluatorTag) (inputs.map (LiteralNumeralPrefix.numeralCall J.numeralTag)))
  (LiteralNumeralPrefix.numeralCall J.numeralTag (call evaluatorTag inputs))
def childCode {ctx n : Nat} (producerTag evaluatorTag : Nat) (inputs : List.Vector (Term ctx) n) : Term ctx :=
 call producerTag (Term.numeral evaluatorTag ::ᵥ inputs)
def stepInputs {ctx m : Nat} (qTag : Nat) (counter : Term ctx) (inputs : List.Vector (Term ctx) m) : List.Vector (Term ctx) (m+2) :=
 counter ::ᵥ call qTag (counter ::ᵥ inputs) ::ᵥ inputs
/-- Public formula and code preserve actual qTag and input order. -/
def formulaCall {ctx m : Nat} (formulaTag qTag : Nat) (counter : Term ctx) (inputs : List.Vector (Term ctx) m) : Term ctx :=
 call formulaTag (Term.numeral qTag ::ᵥ counter ::ᵥ inputs)
def producerCall {ctx m : Nat} (producerTag qTag : Nat) (counter : Term ctx) (inputs : List.Vector (Term ctx) m) : Term ctx :=
 call producerTag (Term.numeral qTag ::ᵥ counter ::ᵥ inputs)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore
