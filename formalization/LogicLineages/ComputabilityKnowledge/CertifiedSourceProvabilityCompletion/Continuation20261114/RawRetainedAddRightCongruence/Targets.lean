module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAddRightCongruence.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAddRightCongruence.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
/-- The original AddRight singleton, genuinely rebuilt at the newest AddLeft checker.
Only its three validators are assumptions; no old or new CORE success premise. -/
def InternalReplacement : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t u v index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (RawReflexivityDispatcher.valid I.validatorTag t)
  (.imp (RawReflexivityDispatcher.valid I.validatorTag u)
   (.imp (RawReflexivityDispatcher.valid I.validatorTag v)
    (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
     (.add (RawAddRightReplace.formulaValue I.consTag I.appendTag t u v)
      (RawAddRightReplace.formulaValue I.consTag I.appendTag t u v))
     (RawAddRightCertificate.certificate I.consTag I.rightLineTag t u v)) (.succ .zero))))))
/-- Genuine t=u implies t+v=u+v via original replacement, constructed reflexivity,
and two canonical MP certificates at one checker and runtime. -/
def InternalCongruence : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t u v input index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (RawReflexivityDispatcher.valid I.validatorTag t)
  (.imp (RawReflexivityDispatcher.valid I.validatorTag u)
   (.imp (RawReflexivityDispatcher.valid I.validatorTag v)
    (.imp (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
     (.add (RawAddRightCongruence.eqRaw I.consTag I.appendTag t u) (RawAddRightCongruence.eqRaw I.consTag I.appendTag t u)) input) (.succ .zero))
     (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
      (.add (RawAddRightCongruence.outputRaw I.consTag I.appendTag t u v) (RawAddRightCongruence.outputRaw I.consTag I.appendTag t u v))
      (RawAddRightCongruence.certificate I.mpTag I.rightLineTag I.reflexivityTag I.consTag I.appendTag t u v input)) (.succ .zero)))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedAddRightCongruence.Targets
