module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAdditionEvaluation.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAdditionEvaluation.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
def InternalCongruence : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t t' u u' first second index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (RawReflexivityDispatcher.valid I.validatorTag t)
  (.imp (RawReflexivityDispatcher.valid I.validatorTag t')
   (.imp (RawReflexivityDispatcher.valid I.validatorTag u)
    (.imp (RawReflexivityDispatcher.valid I.validatorTag u')
     (.imp (RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel t t' first)
      (.imp (RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel u u' second)
       (RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel
        (RawAddRightCongruence.addRaw I.consTag I.appendTag t u)
        (RawAddRightCongruence.addRaw I.consTag I.appendTag t' u')
        (congruenceCertificate I.mpTag I.addLeftLineTag I.addRightLineTag I.equalityLineTag I.reflexivityTag I.consTag I.appendTag
         t t' u u' first second)))))))))
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
      (certificate I.mpTag I.addLeftLineTag I.addRightLineTag I.equalityLineTag I.reflexivityTag
       I.consTag I.appendTag I.numeralTag I.iteratorTag I.rightTag t u m k first second)))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAdditionEvaluation.Targets
