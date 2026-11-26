module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
/-- The actual closed literal argument of published prD. -/
def argument (pF : Program 1) (c : Code) (sigma : Sentence) : Term 0 :=
 GorbowBooleanTruth.binaryCodeTerm 0
  (Term.numeral (GorbowSortedSyntaxCode.formulaCode (rho pF c)))
  (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma))
def leftArgs {ctx : Nat} (K : Tags) (pF : Program 1) (c : Code) (sigma : Sentence)
 (innerFuel innerCert : Term ctx) : List.Vector (Term ctx) 5 :=
 LiteralNumeralPrefix.numeralCall K.numeralTag (Term.numeral (Encodable.encode c)) ::ᵥ
 LiteralNumeralPrefix.numeralCall K.numeralTag innerFuel ::ᵥ
 LiteralNumeralPrefix.numeralCall K.numeralTag .zero ::ᵥ
 Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (argument pF c sigma))) ::ᵥ
 LiteralNumeralPrefix.numeralCall K.numeralTag innerCert ::ᵥ nil
def value {ctx : Nat} (pF : Program 1) (c : Code) (sigma : Sentence) : Term ctx :=
 GorbowBooleanTruth.binaryCodeTerm 0
  (Term.numeral (GorbowSortedSyntaxCode.formulaCode (rho pF c)))
  (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma))
def rightArgs {ctx : Nat} (K : Tags) (pF : Program 1) (c : Code) (sigma : Sentence)
 (innerFuel innerCert : Term ctx) : List.Vector (Term ctx) 5 :=
 (CurrentCheckerSuccessCertificate.checkerInputs c innerFuel (value pF c sigma) innerCert).map
  (LiteralNumeralPrefix.numeralCall K.numeralTag)
/-- Genuine call congruence followed by transitivity; no equality between the
syntactically different checkerEquationCode and quotedSuccess is asserted. -/
def certificate {ctx : Nat} (K : Tags) (pF : Program 1) (c : Code) (sigma : Sentence)
 (innerFuel innerCert literalProof checkerProof : Term ctx) : Term ctx :=
 let xs := leftArgs K pF c sigma innerFuel innerCert
 let ys := rightArgs K pF c sigma innerFuel innerCert
 let codes := reflexivityCertificate K (xs.get 0) ::ᵥ reflexivityCertificate K (xs.get 1) ::ᵥ
  reflexivityCertificate K (xs.get 2) ::ᵥ literalProof ::ᵥ reflexivityCertificate K (xs.get 4) ::ᵥ nil
 let tag := Term.numeral (GorbowNamedInternalProvability.checkerTag pF)
 transitivityCertificate K.mtag K.ctag K.atag K.constructorTag
  (callValue K tag xs) (callValue K tag ys) (LiteralNumeralPrefix.numeralCall K.numeralTag (.succ .zero))
  (callCertificate K tag xs ys codes) checkerProof

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge
