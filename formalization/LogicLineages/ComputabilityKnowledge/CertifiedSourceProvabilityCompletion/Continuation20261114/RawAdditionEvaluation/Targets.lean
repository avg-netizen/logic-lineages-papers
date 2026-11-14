module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionEvaluation.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionEvaluation.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
/-- Genuine structural addition evaluation: two arbitrary raw operand evaluations
produce their sum's numeral computation at the identical actual checker/runtime.
The closed numeral validators and numeral-sum acceptance must be derived, not assumed. -/
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
      (RawAdditionComputation.addRaw I.consTag I.appendTag t u)
      (LiteralNumeralPrefix.numeralCall I.numeralTag (.add m k))
      (certificate I.mpTag I.qtag I.rightLineTag I.equalityLineTag I.reflexivityTag
       I.consTag I.appendTag I.numeralTag I.iteratorTag I.rightTag t u m k first second)))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionEvaluation.Targets
