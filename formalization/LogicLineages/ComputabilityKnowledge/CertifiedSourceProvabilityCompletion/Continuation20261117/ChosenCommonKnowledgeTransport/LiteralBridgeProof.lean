module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.ChosenCommonKnowledgeTransport.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.LiteralProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.ChosenCommonKnowledgeTransport.LiteralBridgeProof
open GorbowSyntax GorbowTheoryProof GorbowSortedSyntaxCode

/-- Eliminate the top-selector guard x=x by ordinary reflexivity. This is
a proof between the original distinct quantified formulas, not code equality. -/
theorem topSelectedToAll (T : Sentence → Prop) (sigma : Sentence) :
    Nonempty (Derivation T
      (.imp (everyone topSelector (formulaCode sigma))
        (GorbowSortedRevisionEventual.allAgentsKnow sigma))) := by
  let E := everyone topSelector (formulaCode sigma)
  let B := GorbowClosedDeduction.extend T E
  let ag : Formula 1 := .agent (.var 0)
  let kn : Formula 1 := .knowledge (.var 0) (Term.numeral (formulaCode sigma))
  let top : Formula 1 := .equal (.var 0) (.var 0)
  obtain ⟨hSelected⟩ := CertifiedSourceProvabilityCompletion.Proof.openUniversal
    (T := B) (.imp ag (.imp top kn)) (.axiom E (Or.inr rfl))
  have hTop : Derivation B top := .logical (.reflexive _)
  have hAllBody : Derivation B (.imp ag kn) :=
    Hilbert.mpUnder hSelected (Hilbert.lift ag hTop)
  have hAll : Derivation B (GorbowSortedRevisionEventual.allAgentsKnow sigma) :=
    .generalize hAllBody
  obtain ⟨h⟩ := GorbowClosedDeductionProof.deduction T E 0 _ hAll
  exact ⟨by simpa only [GorbowClosedDeductionProof.closedSyntax.1] using h⟩

theorem displayedThetaReverse : Targets.DisplayedThetaReverse := by
  intro T
  let E := everyone topSelector (formulaCode falseEquality)
  obtain ⟨hAll⟩ := topSelectedToAll T falseEquality
  have hE : Hilbert.Local T 0 [E, literalTheta] E :=
    .hypothesis List.mem_cons_self
  have hTheta : Hilbert.Local T 0 [E, literalTheta] literalTheta :=
    .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  have hFalse : Hilbert.Local T 0 [E, literalTheta] falseEquality :=
    .mp hTheta (.mp (.base hAll) hE)
  exact ⟨Hilbert.Local.finish
    (Hilbert.Local.discharge (Hilbert.Local.discharge hFalse))⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.ChosenCommonKnowledgeTransport.LiteralBridgeProof

#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.ChosenCommonKnowledgeTransport.LiteralBridgeProof
