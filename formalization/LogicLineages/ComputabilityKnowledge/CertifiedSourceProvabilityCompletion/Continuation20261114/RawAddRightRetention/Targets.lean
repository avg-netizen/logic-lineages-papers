module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddRightRetention.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddRightRetention.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
/-- Actual outer AddRightReplace bounded-search selector retains every internally accepted line
of its literal old leaf. No native calibration or recognizer failure premise. -/
def InternalRetention : Prop := ∀ n (p : Program n) (old : Program 1) (oldTag newTag : Nat),
 (nodes p)[oldTag]? = some ⟨1,old⟩ →
 (nodes p)[newTag]? = some ⟨1,RawAddRightReplace.logicalLeaf old⟩ →
 ∀ ctx (line : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (RawLogicalRetention.leafCall oldTag line) (.succ .zero))
   (.equal (RawLogicalRetention.leafCall newTag line) (.succ .zero))))

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
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddRightRetention.Targets
