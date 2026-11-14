module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestTransitivity.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestTransitivity.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
/-- The original equality-right-replacement singleton, genuinely rebuilt at the newest MulLeft checker.
Only its three validators are assumptions; no old or new CORE success premise. -/
def InternalReplacement : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t u v index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (RawReflexivityDispatcher.valid I.validatorTag t)
  (.imp (RawReflexivityDispatcher.valid I.validatorTag u)
   (.imp (RawReflexivityDispatcher.valid I.validatorTag v)
    (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
     (.add (RawRightReplace.formulaValue I.consTag I.appendTag t u v)
      (RawRightReplace.formulaValue I.consTag I.appendTag t u v))
     (RawRightReplaceCertificate.certificate I.consTag I.equalityLineTag t u v)) (.succ .zero))))))
/-- Four actual MPs compose input equalities through symmetry and original
right replacement, at the identical runtime and actual common checker. -/
def InternalTransitivity : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t u v first second index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.validatorTag t)
   (.imp (RawReflexivityDispatcher.valid I.validatorTag u)
    (.imp (RawReflexivityDispatcher.valid I.validatorTag v)
     (.imp (RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel t u first)
      (.imp (RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel u v second)
       (RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel t v
        (RawEqualityComposition.transitivityCertificate I.mpTag I.equalityLineTag I.reflexivityTag I.consTag I.appendTag t u v first second))))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestTransitivity.Targets
