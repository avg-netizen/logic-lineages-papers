module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestMultiplicationComputation.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestMultiplicationComputation.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
/-- Actual original mul-zero certificate at the common arithmetic checker. -/
def InternalBase : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.validatorTag t)
   (RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel
    (mulRaw I.consTag I.appendTag t (RawAdditionComputation.zeroRaw I.consTag))
    (RawAdditionComputation.zeroRaw I.consTag)
    (RawMultiplicationCertificates.ZeroCertificate.certificate I.consTag I.mulZeroTag t))))
/-- Genuine multiplication computation step for an arbitrary raw right operand.
Input product=num(z) is transported through the actual addition evaluator and
arbitrary-count congruence to product(next)=num(z+m). No step-success premise. -/
def InternalStep : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (m u z cert index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.validatorTag u)
   (.imp (RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel
     (mulRaw I.consTag I.appendTag (LiteralNumeralPrefix.numeralCall I.numeralTag m) u)
     (LiteralNumeralPrefix.numeralCall I.numeralTag z) cert)
    (RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel
     (mulRaw I.consTag I.appendTag (LiteralNumeralPrefix.numeralCall I.numeralTag m)
      (RawAdditionComputation.succRaw I.consTag u))
     (LiteralNumeralPrefix.numeralCall I.numeralTag (.add z m))
     (stepCertificate I.mpTag I.equalityLineTag I.reflexivityTag I.mulSuccTag I.iteratorTag
      I.congruenceIteratorTag I.numeralTag I.prefixTag I.pairTag I.consTag I.appendTag I.rightTag m u z cert)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestMultiplicationComputation.Targets
