module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAdditionIteration.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAdditionIteration.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof
/-- Actual arbitrary-count computation: concrete numeral and result syntax,
with the certificate extracted from the same PR iterator. No step-success premise. -/
def InternalIteration : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (count t index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.validatorTag t)
   (.conj (.equal (RawIteratedSucc.first I.leftTag (binaryCall I.iteratorTag count t))
     (SixSol20261113.LiteralNumeralPrefix.numeralCall I.numeralTag count))
    (.conj (.equal (RawIteratedSucc.second I.leftTag I.rightTag (binaryCall I.iteratorTag count t))
      (binaryCall I.prefixTag count t))
     (.conj (RawReflexivityDispatcher.valid I.validatorTag (binaryCall I.prefixTag count t))
      (RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel
       (RawAdditionComputation.addRaw I.consTag I.appendTag t (SixSol20261113.LiteralNumeralPrefix.numeralCall I.numeralTag count))
       (binaryCall I.prefixTag count t)
       (RawIteratedSucc.third I.rightTag (binaryCall I.iteratorTag count t))))))))
/-- Original numeral addition at the new arithmetic checker, not an old-interface cast.
The certificate remains the third projection of the identical PR iterator. -/
def InternalNumeralAddition : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (m k index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel
   (RawAdditionComputation.addRaw I.consTag I.appendTag
    (SixSol20261113.LiteralNumeralPrefix.numeralCall I.numeralTag m)
    (SixSol20261113.LiteralNumeralPrefix.numeralCall I.numeralTag k))
   (SixSol20261113.LiteralNumeralPrefix.numeralCall I.numeralTag (.add m k))
   (RawIteratedSucc.third I.rightTag (binaryCall I.iteratorTag k
    (SixSol20261113.LiteralNumeralPrefix.numeralCall I.numeralTag m)))))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAdditionIteration.Targets
