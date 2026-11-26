module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestSuccIteration.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestSuccIteration.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
/-- Actual PR state constructor performs precisely one successor-prefix update
and the paid original two-MP certificate construction. No acceptance premise. -/
def InternalStep : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t u cert : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (stepCall I.stepTag (state I.pairTag t u cert))
   (state I.pairTag (RawSuccReplace.succValue I.consTag t) (RawSuccReplace.succValue I.consTag u)
    (RawSuccCongruence.certificate I.mpTag I.replaceTag I.reflexivityTag I.consTag I.appendTag t u cert))))
/-- Genuine internal arbitrary-count congruence with exact successor-prefix
component identities. Same checker and runtime; no per-step success premise. -/
def InternalIteration : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (count t u cert index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.validatorTag t)
   (.imp (RawReflexivityDispatcher.valid I.validatorTag u)
    (.imp (RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel t u cert)
     (.conj (.equal (first I.leftTag (iteratorCall I.iteratorTag count (state I.pairTag t u cert)))
       (RawAdditionIteration.binaryCall I.prefixTag count t))
      (.conj (.equal (second I.leftTag I.rightTag (iteratorCall I.iteratorTag count (state I.pairTag t u cert)))
        (RawAdditionIteration.binaryCall I.prefixTag count u))
       (.conj (RawReflexivityDispatcher.valid I.validatorTag (RawAdditionIteration.binaryCall I.prefixTag count t))
        (.conj (RawReflexivityDispatcher.valid I.validatorTag (RawAdditionIteration.binaryCall I.prefixTag count u))
         (RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel
          (RawAdditionIteration.binaryCall I.prefixTag count t)
          (RawAdditionIteration.binaryCall I.prefixTag count u)
          (third I.rightTag (iteratorCall I.iteratorTag count (state I.pairTag t u cert))))))))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestSuccIteration.Targets
