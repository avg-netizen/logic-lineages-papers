module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawLogicalRetention.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawLogicalRetention.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
/-- Actual outer RightReplace selector retains every internally accepted line
of its literal old leaf. No native calibration or recognizer failure premise. -/
def InternalRetention : Prop := ∀ n (p : Program n) (old : Program 1) (oldTag newTag : Nat),
 (nodes p)[oldTag]? = some ⟨1,old⟩ →
 (nodes p)[newTag]? = some ⟨1,RawRightReplace.logicalLeaf old⟩ →
 ∀ ctx (line : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (leafCall oldTag line) (.succ .zero))
   (.equal (leafCall newTag line) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawLogicalRetention.Targets
