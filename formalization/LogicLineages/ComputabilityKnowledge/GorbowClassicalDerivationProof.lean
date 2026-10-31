module

public import LogicLineages.ComputabilityKnowledge.GorbowClassicalDerivationTargets
public import LogicLineages.ComputabilityKnowledge.GorbowClosedDeductionProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowClassicalDerivation.Proof
open GorbowSyntax GorbowTheoryProof GorbowClosedDeduction

theorem explosion : Targets.Explosion := by
  intro A p q hp hn
  have h : Derivation A (.imp (.neg q) (.neg p)) :=
    .mp (.logical (.k (.neg p) (.neg q))) hn
  have hi : Derivation A (.imp p q) :=
    .mp (.logical (.classicalContraposition q p)) h
  exact ⟨.mp hi hp⟩

private theorem branchAssumption (A : Sentence → Prop) (p : Sentence) :
    Nonempty (Derivation (contradictionBranch A p) (.neg p)) := by
  have h : contradictionBranch A p (.neg p) := Or.inr rfl
  exact ⟨by simpa only [GorbowClosedDeductionProof.closedSyntax.1] using
    (Derivation.axiom (A:=contradictionBranch A p) (n:=0) (.neg p) h)⟩

private theorem branchLift (A : Sentence → Prop) (p q : Sentence) (h : Derivation A q) :
    Nonempty (Derivation (contradictionBranch A p) q) :=
  GorbowTheoryProofProof.monotonicity A (contradictionBranch A p)
    (fun _ h => Or.inl h) 0 q ⟨h⟩

theorem closedReductio : Targets.ClosedReductio := by
  intro A p hp
  let t : Sentence := .equal .zero .zero
  obtain ⟨hn⟩ := branchAssumption A p
  obtain ⟨hnt⟩ := explosion (contradictionBranch A p) p (.neg t) hp hn
  obtain ⟨hd⟩ := GorbowClosedDeductionProof.deduction A (.neg p) 0 (.neg t) hnt
  have hi : Derivation A (.imp (.neg p) (.neg t)) := by
    simpa only [GorbowClosedDeductionProof.closedSyntax.1] using hd
  have ht : Derivation A (.imp t p) :=
    .mp (.logical (.classicalContraposition p t)) hi
  exact ⟨.mp ht (.logical (.reflexive .zero))⟩

theorem doubleNegationElimination : Targets.DoubleNegationElimination := by
  intro A p hnn
  obtain ⟨hn⟩ := branchAssumption A p
  obtain ⟨hnn'⟩ := branchLift A p (.neg (.neg p)) hnn
  obtain ⟨hp⟩ := explosion (contradictionBranch A p) (.neg p) p hn hnn'
  exact closedReductio A p hp

theorem modusTollens : Targets.ModusTollens := by
  intro A p q hi hnq
  obtain ⟨hnnp⟩ := branchAssumption A (.neg p)
  obtain ⟨hp⟩ := doubleNegationElimination (contradictionBranch A (.neg p)) p hnnp
  obtain ⟨hi'⟩ := branchLift A (.neg p) (.imp p q) hi
  obtain ⟨hnq'⟩ := branchLift A (.neg p) (.neg q) hnq
  obtain ⟨hnp⟩ := explosion (contradictionBranch A (.neg p)) q (.neg p) (.mp hi' hp) hnq'
  exact closedReductio A (.neg p) hnp

end LogicLineages.ComputabilityKnowledge.GorbowClassicalDerivation.Proof
