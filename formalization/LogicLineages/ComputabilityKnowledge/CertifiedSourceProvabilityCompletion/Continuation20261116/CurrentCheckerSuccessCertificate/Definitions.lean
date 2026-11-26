module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCheckerSuccessCertificate
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
/-- EXACT five inputs to original published provability's checker. Inner fuel
is the arbitrary witnessed checker fuel, not the outer compiled-proof bound. -/
def checkerInputs {ctx : Nat} (c : Code) (innerFuel formula certificate : Term ctx) : List.Vector (Term ctx) 5 :=
 Term.numeral (Encodable.encode c) ::ᵥ innerFuel ::ᵥ .zero ::ᵥ formula ::ᵥ certificate ::ᵥ nil
/-- Literal original checker equation, as an object-language antecedent. -/
def success {ctx : Nat} (pF : Program 1) (c : Code) (innerFuel formula certificate : Term ctx) : Formula ctx :=
 .equal (call (GorbowNamedInternalProvability.checkerTag pF) (checkerInputs c innerFuel formula certificate)) (.succ .zero)
/-- Raw formula-code term for the closed numerical checker equation, with
actual numeral quotation of ALL five runtime arguments and fixed RHS 1.
This is not the quotation of the arbitrary open antecedent syntax. -/
def quotedSuccess {ctx : Nat} (J : Tags) (pF : Program 1) (c : Code)
 (innerFuel formula certificate : Term ctx) : Term ctx :=
 equalValue J.ctag J.atag
  (callValue J (Term.numeral (GorbowNamedInternalProvability.checkerTag pF))
   ((checkerInputs c innerFuel formula certificate).map (LiteralNumeralPrefix.numeralCall J.numeralTag)))
  (LiteralNumeralPrefix.numeralCall J.numeralTag (.succ .zero))
/-- Actual compiler output, with canonical checker occurrence as runtime target. -/
def proofCode {ctx : Nat} (producerTag : Nat) (pF : Program 1) (c : Code)
 (innerFuel formula certificate : Term ctx) : Term ctx :=
 CurrentStructuralProducerCore.code producerTag (GorbowNamedInternalProvability.checkerTag pF)
  (checkerInputs c innerFuel formula certificate)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCheckerSuccessCertificate
