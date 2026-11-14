module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccIteration.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccIteration.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
/-- Actual PR state constructor performs precisely one successor-prefix update
and the paid original two-MP certificate construction. No acceptance premise. -/
def InternalStep : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t u cert : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (stepCall I.stepTag (state I.ptag t u cert))
   (state I.ptag (RawSuccReplace.succValue I.ctag t) (RawSuccReplace.succValue I.ctag u)
    (RawSuccCongruence.certificate I.mpTag I.replaceTag I.reflexivityTag I.ctag I.atag t u cert))))
/-- Genuine internal arbitrary-count congruence with exact successor-prefix
component identities. Same checker and runtime; no per-step success premise. -/
def InternalIteration : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (count t u cert index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.vtag t)
   (.imp (RawReflexivityDispatcher.valid I.vtag u)
    (.imp (RawEqualityComposition.accepted I.qctag I.ctag I.atag index fuel t u cert)
     (.conj (.equal (first I.leftTag (iteratorCall I.iteratorTag count (state I.ptag t u cert)))
       (RawAdditionIteration.binaryCall I.prefixTag count t))
      (.conj (.equal (second I.leftTag I.rightTag (iteratorCall I.iteratorTag count (state I.ptag t u cert)))
        (RawAdditionIteration.binaryCall I.prefixTag count u))
       (.conj (RawReflexivityDispatcher.valid I.vtag (RawAdditionIteration.binaryCall I.prefixTag count t))
        (.conj (RawReflexivityDispatcher.valid I.vtag (RawAdditionIteration.binaryCall I.prefixTag count u))
         (RawEqualityComposition.accepted I.qctag I.ctag I.atag index fuel
          (RawAdditionIteration.binaryCall I.prefixTag count t)
          (RawAdditionIteration.binaryCall I.prefixTag count u)
          (third I.rightTag (iteratorCall I.iteratorTag count (state I.ptag t u cert)))))))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccIteration.Targets
