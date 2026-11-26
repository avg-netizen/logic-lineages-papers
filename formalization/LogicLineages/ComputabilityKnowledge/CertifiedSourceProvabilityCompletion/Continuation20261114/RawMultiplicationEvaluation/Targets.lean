module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationEvaluation.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationEvaluation.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
/-- Genuine structural multiplication evaluation: two arbitrary raw operand evaluations
produce their product's numeral computation at the identical actual checker/runtime.
The closed numeral validators and numeral-product acceptance must be derived, not assumed. -/
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
      (certificate I.mpTag I.qtag I.rightLineTag I.equalityLineTag I.reflexivityTag
       I.consTag I.appendTag I.numeralTag I.mulIteratorTag I.rightTag t u m k first second)))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationEvaluation.Targets
