module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCommonKnowledgeCounterexample.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.LogicalSupportProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCommonKnowledgeCounterexample.KTTransportProof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB

/-- KT's original axioms remain available with either optional-UBF flag.
The impossible false-Barcan constructor introduces no new source assumption. -/
theorem axiomInclusion (pF pR : Program 1) (q : Program 5) (c : Code)
    (withUBF : Bool) (sigma : Sentence) :
    GorbowPublishedKT.Axiom false pF pR q c sigma →
      GorbowPublishedKT.Axiom withUBF pF pR q c sigma := by
  intro h
  cases h with
  | d sigma hd => exact .d sigma hd
  | negation => exact .negation
  | implication => exact .implication
  | conjunction => exact .conjunction
  | disjunction => exact .disjunction
  | universal => exact .universal
  | existential => exact .existential
  | atomic R names hr hn hc => exact .atomic R names hr hn hc
  | veracity => exact .veracity
  | barcan hFalse => cases hFalse

/-- A structural embedding of the original finite KT trees. The three
theorem-only rules remain applied to global proof premises in both theories. -/
theorem proofInclusion (pF pR : Program 1) (q : Program 5) (c : Code)
    (withUBF : Bool) {n : Nat} {phi : Formula n}
    (h : GorbowPublishedKT.Proof false pF pR q c phi) :
    Nonempty (GorbowPublishedKT.Proof withUBF pF pR q c phi) := by
  induction h with
  | ordinary d =>
      obtain ⟨d'⟩ := GorbowTheoryProofProof.monotonicity
        (GorbowPublishedKT.Axiom false pF pR q c)
        (GorbowPublishedKT.Axiom withUBF pF pR q c)
        (axiomInclusion pF pR q c withUBF) _ _ ⟨d⟩
      exact ⟨.ordinary d'⟩
  | mp p r ihp ihr =>
      obtain ⟨p'⟩ := ihp
      obtain ⟨r'⟩ := ihr
      exact ⟨.mp p' r'⟩
  | generalize p ih =>
      obtain ⟨p'⟩ := ih
      exact ⟨.generalize p'⟩
  | truthIntroduction p ih =>
      obtain ⟨p'⟩ := ih
      exact ⟨.truthIntroduction p'⟩
  | truthElimination p ih =>
      obtain ⟨p'⟩ := ih
      exact ⟨.truthElimination p'⟩
  | knowledgeNecessitation p ih =>
      obtain ⟨p'⟩ := ih
      exact ⟨.knowledgeNecessitation p'⟩

/-- A pure ordinary theorem suitable for application to a KT proof of
P -> Q. Its local assumptions are discharged before any KT rule is used. -/
theorem implicationToNegation (T : Sentence → Prop) {n : Nat} (P Q : Formula n)
    (hNotQ : Derivation T (.neg Q)) :
    Nonempty (Derivation T (.imp (.imp P Q) (.neg P))) := by
  have hP : Hilbert.Local T n [.neg (.neg P), .imp P Q] P :=
    .mp (.base (Hilbert.doubleNegation P)) (.hypothesis List.mem_cons_self)
  have hImp : Hilbert.Local T n [.neg (.neg P), .imp P Q] (.imp P Q) :=
    .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  have hNotP : Hilbert.Local T n [.imp P Q] (.neg P) :=
    Hilbert.Local.classical (.neg P)
      (Hilbert.Local.explosion (.neg P) (.mp hImp hP) (.base hNotQ))
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hNotP)⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCommonKnowledgeCounterexample.KTTransportProof

#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCommonKnowledgeCounterexample.KTTransportProof
