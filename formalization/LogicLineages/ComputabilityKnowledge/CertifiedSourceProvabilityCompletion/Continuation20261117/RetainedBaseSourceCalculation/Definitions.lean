module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseProducerInstallation.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseSourceCalculation
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence


def rawCall {ctx : Nat} (K : PrescribedRuntimeCallCongruence.Tags) (tag : Nat) (value : Term ctx) : Term ctx :=
 CorrectedAugmentationErasure.left K tag value

def peelCall {n ctx : Nat} (producerTag target : Nat) (p : Program 1) (q : Program n) (value : Term ctx) : Term ctx :=
 call producerTag (Term.numeral target ::ᵥ
  Term.numeral (argumentTag (.projection (0 : Fin 2)) (CorrectedAugmentationErasure.branches p q) 1) ::ᵥ value ::ᵥ nil)

/-- Literal nested transitivity certificate consuming the three actual Program3
calls; no successful certificate is supplied as a premise. -/
def peelCertificate {ctx : Nat} (K : PrescribedRuntimeCallCongruence.Tags)
 (pF0 : Program 1) (pCK : Program 2) (box : Program 6) (outer : Program 5)
 (peelTag : Nat) (value : Term ctx) : Term ctx :=
 let inner := GorbowNamedInternalProvability.augment pF0 pCK
 let pF := GorbowNamedInternalProvability.augment inner box
 let c68 := peelCall peelTag 6 pF outer value
 let c810 := peelCall peelTag 8 inner box value
 let c1012 := peelCall peelTag 10 pF0 pCK value
 let c610 := transitivityCertificate K.mtag K.ctag K.atag K.constructorTag
  (rawCall K 6 value) (rawCall K 8 value) (rawCall K 10 value) c68 c810
 transitivityCertificate K.mtag K.ctag K.atag K.constructorTag
  (rawCall K 6 value) (rawCall K 10 value) (rawCall K 12 value) c610 c1012

/-- Final code uses compile(pF0) at the retained base occurrence12, NEVER
compile(final pF). Ordinary defining-equation equality transports the output
from call12 to call6 without changing this certificate term. -/
def certificate {ctx : Nat} (K : PrescribedRuntimeCallCongruence.Tags)
 (pF0 : Program 1) (pCK : Program 2) (box : Program 6) (outer : Program 5)
 (peelTag baseProducerTag : Nat) (value : Term ctx) : Term ctx :=
 transitivityCertificate K.mtag K.ctag K.atag K.constructorTag
  (rawCall K 6 value) (rawCall K 12 value)
  (LiteralNumeralPrefix.numeralCall K.numeralTag (call 12 (value ::ᵥ nil)))
  (peelCertificate K pF0 pCK box outer peelTag value)
  (CurrentStructuralProducerCore.code baseProducerTag 12 (value ::ᵥ nil))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseSourceCalculation
