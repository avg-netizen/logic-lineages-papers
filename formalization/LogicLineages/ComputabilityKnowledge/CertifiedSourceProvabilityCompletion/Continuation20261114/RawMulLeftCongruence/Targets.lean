module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulLeftCongruence.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulLeftCongruence.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
/-- Actual reflexivity singleton is reconstructed at the newest checker via
all prior logical selectors and new rule0 CORE retention, not an old CORE cast. -/
def InternalReflexivity : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (RawReflexivityDispatcher.valid I.validatorTag t)
  (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
   (.add (RawReflexivity.equalityValue I.consTag I.appendTag t) (RawReflexivity.equalityValue I.consTag I.appendTag t))
   (RawCumulativeLogical.certificate I.consTag I.reflexivityTag t)) (.succ .zero))))
/-- Genuine t=u implies v*t=v*u via original replacement, constructed reflexivity,
and two canonical MP certificates at one checker and runtime. -/
def InternalCongruence : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t u v input index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (RawReflexivityDispatcher.valid I.validatorTag t)
  (.imp (RawReflexivityDispatcher.valid I.validatorTag u)
   (.imp (RawReflexivityDispatcher.valid I.validatorTag v)
    (.imp (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
     (.add (eqRaw I.consTag I.appendTag t u) (eqRaw I.consTag I.appendTag t u)) input) (.succ .zero))
     (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
      (.add (outputRaw I.consTag I.appendTag t u v) (outputRaw I.consTag I.appendTag t u v))
      (certificate I.mpTag I.qtag I.reflexivityTag I.consTag I.appendTag t u v input)) (.succ .zero)))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulLeftCongruence.Targets
