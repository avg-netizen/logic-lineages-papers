module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.LiteralTargets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.FiniteIterationProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.LiteralProof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB

theorem displayedThetaBridge : LiteralTargets.DisplayedThetaBridge := by
  intro T
  let K := GorbowSortedRevisionEventual.allAgentsKnow falseEquality
  obtain ⟨hk⟩ := Proof.allKnowToSelected T topSelector falseEquality
  have hK : Hilbert.Local T 0 [K, sourceTheta] K := .hypothesis List.mem_cons_self
  have hOld : Hilbert.Local T 0 [K, sourceTheta] sourceTheta :=
    .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  have hb : Hilbert.Local T 0 [K, sourceTheta] falseEquality :=
    .mp hOld (.mp (.base hk) hK)
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hb))⟩

theorem literalDirectTheta : LiteralTargets.LiteralDirectTheta := by
  intro pF pR q c hA
  obtain ⟨hb⟩ := displayedThetaBridge (GorbowPublishedKT.Axiom false pF pR q c)
  obtain ⟨hOld⟩ := Proof.directTheta pF pR q c hA
  exact ⟨.mp (.ordinary hb) hOld⟩

/-- The numeral code changes to that of the actual preceding literal
sentence at every step. No v1/literal code equality is assumed. -/
theorem literalFiniteIteration : LiteralTargets.LiteralFiniteIteration := by
  intro pF pR q c hA r
  induction r with
  | zero => exact literalDirectTheta pF pR q c hA
  | succ r ih =>
      obtain ⟨h⟩ := ih
      exact ⟨Proof.selectedNecessitation topSelector h⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.LiteralProof
