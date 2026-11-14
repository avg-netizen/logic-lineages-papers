module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnaryEvaluation.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnaryEvaluation.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
/-- Original zero raw term computes to original numeral zero, with the literal
reflexivity singleton; neither numeral identity nor acceptance is assumed. -/
def InternalZero : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel
   (RawAdditionComputation.zeroRaw I.consTag)
   (LiteralNumeralPrefix.numeralCall I.numeralTag .zero)
   (RawCumulativeLogical.certificate I.consTag I.reflexivityTag (RawAdditionComputation.zeroRaw I.consTag))))
/-- Actual structural successor evaluation. Only input validity and evaluation
are object-language antecedents; numeral successor identity and checker closure
are proved at the same full checker/runtime. -/
def InternalSuccessor : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t m cert index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.validatorTag t)
   (.imp (RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel t
    (LiteralNumeralPrefix.numeralCall I.numeralTag m) cert)
    (RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel
     (RawAdditionComputation.succRaw I.consTag t)
     (LiteralNumeralPrefix.numeralCall I.numeralTag (.succ m))
     (RawSuccCongruence.certificate I.mpTag I.replaceTag I.reflexivityTag I.consTag I.appendTag
      t (LiteralNumeralPrefix.numeralCall I.numeralTag m) cert)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnaryEvaluation.Targets
