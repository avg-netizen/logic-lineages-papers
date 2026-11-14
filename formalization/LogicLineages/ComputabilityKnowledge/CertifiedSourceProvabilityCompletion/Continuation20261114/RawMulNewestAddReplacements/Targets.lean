module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAddReplacements.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAddReplacements.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
/-- Original three-slot addition-right replacement at the newest multiplication
checker. Three validators only; all recognition, retention, grammar and CODE-bound
singleton execution must be proved internally. -/
def InternalRight : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t u v index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (RawReflexivityDispatcher.valid I.validatorTag t)
  (.imp (RawReflexivityDispatcher.valid I.validatorTag u)
   (.imp (RawReflexivityDispatcher.valid I.validatorTag v)
    (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
     (.add (RawAddRightReplace.formulaValue I.consTag I.appendTag t u v)
      (RawAddRightReplace.formulaValue I.consTag I.appendTag t u v))
     (RawAddRightCertificate.certificate I.consTag I.addRightLineTag t u v)) (.succ .zero))))))
/-- Original three-slot addition-left replacement at the newest multiplication
checker. Three validators only; all recognition, retention, grammar and CODE-bound
singleton execution must be proved internally. -/
def InternalLeft : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t u v index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (RawReflexivityDispatcher.valid I.validatorTag t)
  (.imp (RawReflexivityDispatcher.valid I.validatorTag u)
   (.imp (RawReflexivityDispatcher.valid I.validatorTag v)
    (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
     (.add (RawAddLeftReplace.formulaValue I.consTag I.appendTag t u v)
      (RawAddLeftReplace.formulaValue I.consTag I.appendTag t u v))
     (RawAddLeftCertificate.certificate I.consTag I.addLeftLineTag t u v)) (.succ .zero))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAddReplacements.Targets
