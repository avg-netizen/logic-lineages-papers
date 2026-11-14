module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationProducer.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationProducer.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
/-- Exact internal graph equation, including original binary congruence and actual
numeral-multiplication iterator projection. No semantic reflection. -/
def InternalGraph : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t u m k first second : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.equal (producerCall I.multiplicationProducerTag t u m k first second)
  (RawMultiplicationEvaluation.certificate I.mpTag I.qtag I.rightLineTag I.equalityLineTag I.reflexivityTag
   I.consTag I.appendTag I.numeralTag I.mulIteratorTag I.rightTag t u m k first second)))
def InternalEvaluation : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t u m k first second index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (RawReflexivityDispatcher.valid I.validatorTag t)
  (.imp (RawReflexivityDispatcher.valid I.validatorTag u)
   (.imp (RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel t
    (LiteralNumeralPrefix.numeralCall I.numeralTag m) first)
    (.imp (RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel u
     (LiteralNumeralPrefix.numeralCall I.numeralTag k) second)
     (RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel
      (RawNewestMultiplicationComputation.mulRaw I.consTag I.appendTag t u)
      (LiteralNumeralPrefix.numeralCall I.numeralTag (.mul m k))
      (producerCall I.multiplicationProducerTag t u m k first second)))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationProducer.Targets
