module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawLogicalCoreRetention.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawLogicalCoreRetention.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
/-- Genuine internal old logical acceptance lifts through the actual new
rule0 dispatcher and code-bound singleton run to the actual new CORE.
No success of the new leaf/dispatcher/checker is supplied as a premise. -/
def InternalCoreRetention : Prop := ∀ n (p : Program n) (old arithmetic : Program 1) (x : Program 3)
 (I : Installation p old arithmetic x), ∀ ctx (formula payload args index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (LiteralSyntaxValidator.formulaCall I.ftag .zero formula) (.succ .zero))
   (.imp (.equal (RawLogicalRetention.leafCall I.oldTag (line I.ptag formula payload args)) (.succ .zero))
    (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero (.add formula formula)
     (certificate I.ptag I.ctag formula payload args)) (.succ .zero)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawLogicalCoreRetention.Targets
