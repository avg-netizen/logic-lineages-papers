module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalProducers.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalProducers.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
/-- Exact ORIGINAL logicalLine and singleton numbers. Matrix arities matter:
closed formulas for contraposition, one-variable matrix for existential duality.
Unused second duality input is an arbitrary Nat, not a validity assumption. -/
def Native : Prop :=
 (∀ (a b : Formula 0),
  let args := Encodable.encode (GorbowFormulaPrefixCode.encode a) ::ᵥ Encodable.encode (GorbowFormulaPrefixCode.encode b) ::ᵥ nil
  evaluate (lineConstructor false) args = Encodable.encode (GorbowProofChecker.logicalLine (.classicalContraposition a b)) ∧
  evaluate (singletonConstructor false) args = GorbowNumericCertificate.certificateNumber [GorbowProofChecker.logicalLine (.classicalContraposition a b)]) ∧
 (∀ (a : Formula 1) (unused : Nat),
  let args := Encodable.encode (GorbowFormulaPrefixCode.encode a) ::ᵥ unused ::ᵥ nil
  evaluate (lineConstructor true) args = Encodable.encode (GorbowProofChecker.logicalLine (.existsDualBackward a)) ∧
  evaluate (singletonConstructor true) args = GorbowNumericCertificate.certificateNumber [GorbowProofChecker.logicalLine (.existsDualBackward a)])
/-- Actual symbolic graph, ALL raw argument terms, actual primitive/producer
memberships only. No logical recognizer, validity or CORE acceptance premise. -/
def Internal : Prop := ∀ arity (p : Program arity) (isExists : Bool)
 (ptag ctag atag lineTag singletonTag : Nat), Installation p ptag ctag atag →
 (nodes p)[lineTag]? = some ⟨2,lineConstructor isExists⟩ →
 (nodes p)[singletonTag]? = some ⟨2,singletonConstructor isExists⟩ →
 ∀ ctx (a b : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (lineCall lineTag a b) (lineValue isExists ptag ctag atag a b))) ∧
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (lineCall singletonTag a b) (singletonValue lineTag ctag a b)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalProducers.Targets
