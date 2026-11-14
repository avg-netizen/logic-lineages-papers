module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawArithmeticCoreRetention.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawArithmeticCoreRetention.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
/-- Both actual multiplication selectors preserve every old accepted line internally.
No native calibration, recognizer-failure or old checker premise. -/
def InternalLeafRetention : Prop := ∀ n (p : Program n) (old : Program 1) (oldTag newTag : Nat),
 (nodes p)[oldTag]? = some ⟨1,old⟩ →
 (nodes p)[newTag]? = some ⟨1,RawMultiplication.arithmeticLeaf old⟩ →
 ∀ ctx (line : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (leafCall oldTag line) (.succ .zero))
   (.equal (leafCall newTag line) (.succ .zero))))
/-- Genuine internal old arithmetic acceptance lifts through the actual new
rule1 dispatcher and code-bound singleton run to the actual new CORE.
No success of the new leaf/dispatcher/checker is supplied as a premise. -/
def InternalCoreRetention : Prop := ∀ n (p : Program n) (logical old : Program 1) (x : Program 3)
 (I : Installation p logical old x), ∀ ctx (formula payload args index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (LiteralSyntaxValidator.formulaCall I.ftag .zero formula) (.succ .zero))
   (.imp (.equal (leafCall I.oldTag (line I.ptag formula payload args)) (.succ .zero))
    (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero (.add formula formula)
     (certificate I.ptag I.ctag formula payload args)) (.succ .zero)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawArithmeticCoreRetention.Targets
