module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawIteratedSucc.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawIteratedSucc.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
/-- Actual PR state constructor performs precisely one successor-prefix update
and the paid original two-MP certificate construction. No acceptance premise. -/
def InternalStep : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t u cert : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (stepCall I.stepTag (state I.ptag t u cert))
   (state I.ptag (RawSuccReplace.succValue I.ctag t) (RawSuccReplace.succValue I.ctag u)
    (RawSuccCongruence.certificate I.mpTag I.replaceTag I.qtag I.ctag I.atag t u cert))))
/-- Genuine object-language induction over arbitrary runtime count; the actual
PR iterator preserves both validators and CORE acceptance. Each successor
certificate is proved by two MPs, never assumed. Same checker/index/fuel;
original certificate CODE cutoff remains inside CORE. -/
def InternalIteration : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (count s index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (invariant I.vtag I.qctag I.ctag I.atag I.leftTag I.rightTag index fuel s)
   (invariant I.vtag I.qctag I.ctag I.atag I.leftTag I.rightTag index fuel
    (iteratorCall I.iteratorTag count s))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawIteratedSucc.Targets
