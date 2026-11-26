module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAddCongruences.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAddCongruences.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
/-- Actual original two-MP addition-right congruence at the common newest checker. -/
def InternalRight : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t u v input index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (RawReflexivityDispatcher.valid I.validatorTag t)
  (.imp (RawReflexivityDispatcher.valid I.validatorTag u)
   (.imp (RawReflexivityDispatcher.valid I.validatorTag v)
    (.imp (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
     (.add (RawAddRightCongruence.eqRaw I.consTag I.appendTag t u) (RawAddRightCongruence.eqRaw I.consTag I.appendTag t u)) input) (.succ .zero))
     (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
      (.add (RawAddRightCongruence.outputRaw I.consTag I.appendTag t u v) (RawAddRightCongruence.outputRaw I.consTag I.appendTag t u v))
      (RawAddRightCongruence.certificate I.mpTag I.addRightLineTag I.reflexivityTag I.consTag I.appendTag t u v input)) (.succ .zero)))))))
/-- Actual original two-MP addition-left congruence at the common newest checker. -/
def InternalLeft : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t u v input index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (RawReflexivityDispatcher.valid I.validatorTag t)
  (.imp (RawReflexivityDispatcher.valid I.validatorTag u)
   (.imp (RawReflexivityDispatcher.valid I.validatorTag v)
    (.imp (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
     (.add (RawAddLeftCongruence.eqRaw I.consTag I.appendTag t u) (RawAddLeftCongruence.eqRaw I.consTag I.appendTag t u)) input) (.succ .zero))
     (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
      (.add (RawAddLeftCongruence.outputRaw I.consTag I.appendTag t u v) (RawAddLeftCongruence.outputRaw I.consTag I.appendTag t u v))
      (RawAddLeftCongruence.certificate I.mpTag I.addLeftLineTag I.reflexivityTag I.consTag I.appendTag t u v input)) (.succ .zero)))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAddCongruences.Targets
