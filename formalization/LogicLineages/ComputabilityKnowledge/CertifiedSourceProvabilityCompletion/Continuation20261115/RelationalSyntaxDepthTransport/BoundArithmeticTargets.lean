module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.Targets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.BoundArithmeticTargets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
/-- Success of the original index test survives increasing its bound.
The original difference has argument order (token,bound), computes bound-token,
and is used at the same actual installed registry address on both sides.
The conclusion supplies a genuine internal positive witness, not native nonzero. -/
def DifferencePositiveTransport : Prop := ∀ n (p : Program n) dtag,
 (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩ →
 ∀ ctx (token oldBound newBound positive : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (HistoryBounds.weakBound oldBound newBound)
   (.imp (.equal (HistoryDifference.differenceCall dtag token oldBound) (.succ positive))
    (.ex (HistoryOrder.SupportProof.predBody
     (HistoryDifference.differenceCall dtag token newBound))))))
/-- Binder expansion increments both task bounds. This is a PA derivation
with the same existential nonnegative-gap relation, not a native inequality. -/
def SuccessorBounds : Prop := ∀ (T : Sentence → Prop) ctx (oldBound newBound : Term ctx),
 Nonempty (Derivation T
  (.imp (HistoryBounds.weakBound oldBound newBound)
   (HistoryBounds.weakBound (.succ oldBound) (.succ newBound))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.BoundArithmeticTargets
