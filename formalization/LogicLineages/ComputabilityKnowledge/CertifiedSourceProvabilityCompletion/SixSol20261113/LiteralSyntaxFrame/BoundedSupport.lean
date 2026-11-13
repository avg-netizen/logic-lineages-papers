module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.AppendSupport
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain.BoundSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.BoundedSupport
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryBounds
/-- Arithmetic bounded induction split, with no standard-number interpretation. -/
theorem weakNext (T : Sentence → Prop) {ctx : Nat} (code bound : Term ctx) :
 Nonempty (Derivation T (.imp (weakBound code (.succ bound))
  (.disj (.equal (.succ bound) code) (weakBound code bound)))) := by
 obtain ⟨hs⟩ := HistoryCancellation.TrichotomyProof.weakSplit T code (.succ bound)
 obtain ⟨hw⟩ := HistoryIteratorSuffix.SectorSplitProof.successorWeak T code (.succ bound)
 obtain ⟨hc⟩ := HistoryIteratorDrain.BoundSupportProof.weakSuccessorCancel T code bound
 have hr := Hilbert.compose (.logical (.orRight (.equal (.succ bound) code) (weakBound code bound))) (Hilbert.compose hc hw)
 have hl : Derivation T (.imp (.equal (.succ bound) code) (.disj (.equal (.succ bound) code) (weakBound code bound))) := .logical (.orLeft _ _)
 exact ⟨Hilbert.compose (.mp (.mp (.logical (.orElim _ _ _)) hl) hr) hs⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.BoundedSupport
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxFrame.BoundedSupport
