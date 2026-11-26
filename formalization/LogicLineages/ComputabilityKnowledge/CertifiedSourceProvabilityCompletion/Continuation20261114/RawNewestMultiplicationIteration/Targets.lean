module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestMultiplicationIteration.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestMultiplicationIteration.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
/-- Exact initial constructor, including its actual original mul-zero singleton. -/
def InternalBase : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (m : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (RawAdditionIteration.unaryCall I.mulBaseTag m)
   (RawIteratedSucc.state I.pairTag (RawAdditionComputation.zeroRaw I.consTag) .zero
    (RawMultiplicationCertificates.ZeroCertificate.certificate I.consTag I.mulZeroTag
     (LiteralNumeralPrefix.numeralCall I.numeralTag m)))))
/-- Exact actual successor constructor: arithmetic accumulator z+m and original
checked recursive certificate, not an oracle selecting successful proofs. -/
def InternalStep : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (m u z cert : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (RawAdditionIteration.binaryCall I.mulStepTag m (RawIteratedSucc.state I.pairTag u z cert))
   (RawIteratedSucc.state I.pairTag (RawAdditionComputation.succRaw I.consTag u) (.add z m)
    (RawNewestMultiplicationComputation.stepCertificate I.mpTag I.equalityLineTag I.reflexivityTag I.mulSuccTag I.iteratorTag
     I.congruenceIteratorTag I.numeralTag I.prefixTag I.pairTag I.consTag I.appendTag I.rightTag m u z cert))))
/-- Unconditional internal arbitrary-count numeral multiplication. The actual
PR state records ORIGINAL numeral(k), arithmetic product m*k, and its actual
certificate checked at the same common source tuple/runtime. -/
def InternalIteration : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (m k index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.conj (.equal (RawIteratedSucc.first I.leftTag (RawAdditionIteration.binaryCall I.mulIteratorTag k m))
    (LiteralNumeralPrefix.numeralCall I.numeralTag k))
   (.conj (.equal (RawIteratedSucc.second I.leftTag I.rightTag (RawAdditionIteration.binaryCall I.mulIteratorTag k m)) (.mul m k))
    (RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel
     (RawNewestMultiplicationComputation.mulRaw I.consTag I.appendTag
      (LiteralNumeralPrefix.numeralCall I.numeralTag m) (LiteralNumeralPrefix.numeralCall I.numeralTag k))
     (LiteralNumeralPrefix.numeralCall I.numeralTag (.mul m k))
     (RawIteratedSucc.third I.rightTag (RawAdditionIteration.binaryCall I.mulIteratorTag k m))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestMultiplicationIteration.Targets
