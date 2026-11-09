module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.ThetaProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Proof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB
open GorbowSortedSyntaxCode

/-- Ordinary first-order guard introduction only. This does not use any
necessitation rule while its temporary closed premise is present. -/
theorem allKnowToSelected (T : Sentence → Prop) (A : Selector) (sigma : Sentence) :
    Nonempty (Derivation T (.imp (GorbowSortedRevisionEventual.allAgentsKnow sigma)
      (everyone A (formulaCode sigma)))) := by
  let K := GorbowSortedRevisionEventual.allAgentsKnow sigma
  let B := GorbowClosedDeduction.extend T K
  let ag : Formula 1 := .agent (.var 0)
  let kn : Formula 1 := .knowledge (.var 0) (Term.numeral (formulaCode sigma))
  obtain ⟨hk⟩ := openUniversal (T := B) (.imp ag kn)
    (.axiom K (Or.inr rfl))
  have hi : Derivation B (.imp kn (.imp A.val kn)) := .logical (.k kn A.val)
  have hselected : Derivation B (.imp ag (.imp A.val kn)) := Hilbert.compose hi hk
  have hclosed : Derivation B (everyone A (formulaCode sigma)) := .generalize hselected
  obtain ⟨h⟩ := GorbowClosedDeductionProof.deduction T K 0 _ hclosed
  exact ⟨by simpa only [GorbowClosedDeductionProof.closedSyntax.1] using h⟩

/-- The original KT rule applies only to the already supplied closed global
theorem; the selected-agent wrapper is a separate ordinary theorem. -/
noncomputable def selectedNecessitation {withUBF : Bool} {pF pR : Program 1} {q : Program 5} {c : Code}
    (A : Selector) {sigma : Sentence}
    (h : GorbowPublishedKT.Proof withUBF pF pR q c sigma) :
    GorbowPublishedKT.Proof withUBF pF pR q c (everyone A (formulaCode sigma)) :=
  .mp (.ordinary (Classical.choice (allKnowToSelected
    (GorbowPublishedKT.Axiom withUBF pF pR q c) A sigma))) (.knowledgeNecessitation h)

theorem finiteIteration : Targets.FiniteIteration := by
  intro pF pR q c hA r
  induction r with
  | zero => exact directTheta pF pR q c hA
  | succ r ih =>
      obtain ⟨h⟩ := ih
      exact ⟨selectedNecessitation topSelector h⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Proof
