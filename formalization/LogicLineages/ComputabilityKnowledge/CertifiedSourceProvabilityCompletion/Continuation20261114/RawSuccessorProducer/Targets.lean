module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccessorProducer.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccessorProducer.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
/-- Genuine internal graph equation for the literal executable producer. -/
def InternalGraph : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t m cert : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.equal (producerCall I.producerTag t m cert)
  (RawSuccCongruence.certificate I.mpTag I.replaceTag I.reflexivityTag I.consTag I.appendTag
   t (LiteralNumeralPrefix.numeralCall I.numeralTag m) cert)))
/-- Accepted certificate is the actual producer CALL, not the expanded certificate
assumed successful; graph and numeral transport must be paid internally. -/
def InternalEvaluation : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t m cert index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (RawReflexivityDispatcher.valid I.validatorTag t)
  (.imp (RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel t
   (LiteralNumeralPrefix.numeralCall I.numeralTag m) cert)
   (RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel
    (RawAdditionComputation.succRaw I.consTag t)
    (LiteralNumeralPrefix.numeralCall I.numeralTag (.succ m))
    (producerCall I.producerTag t m cert)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccessorProducer.Targets
