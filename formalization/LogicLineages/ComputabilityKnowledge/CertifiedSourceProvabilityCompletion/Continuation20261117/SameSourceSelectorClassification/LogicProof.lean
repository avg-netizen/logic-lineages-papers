module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.LogicalSupportProof
public import LogicLineages.ComputabilityKnowledge.GorbowBooleanTruth
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceSelectorClassification.LogicProof
open GorbowSyntax GorbowTheoryProof
/-- Pure ordinary classical logic; no source/consistency or semantic premise. -/
theorem complement (T : Sentence → Prop) (E N b : Sentence)
 (hn : Derivation T (.neg b))
 (h : Derivation T (GorbowBooleanTruth.biconditional (.imp E b) N)) :
 Nonempty (Derivation T (GorbowBooleanTruth.biconditional E (.neg N))) := by
 have htN : Derivation T (.imp (.imp E b) N) := .mp (.logical (.andLeft _ _)) h
 have hNt : Derivation T (.imp N (.imp E b)) := .mp (.logical (.andRight _ _)) h
 have hf : Hilbert.Local T 0 [E] (.neg N) := by
  apply Hilbert.Local.classical (.neg N)
  have hN : Hilbert.Local T 0 [.neg (.neg N),E] N :=
   .mp (.base (Hilbert.doubleNegation N)) (.hypothesis List.mem_cons_self)
  have he : Hilbert.Local T 0 [.neg (.neg N),E] E :=
   .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  exact Hilbert.Local.explosion (.neg N) (.mp (.mp (.base hNt) hN) he) (.base hn)
 have hb : Hilbert.Local T 0 [.neg N] E := by
  apply Hilbert.Local.classical E
  have he : Hilbert.Local T 0 [E,.neg E,.neg N] E := .hypothesis List.mem_cons_self
  have hne : Hilbert.Local T 0 [E,.neg E,.neg N] (.neg E) :=
   .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  have ht : Hilbert.Local T 0 [.neg E,.neg N] (.imp E b) :=
   (Hilbert.Local.explosion b he hne).discharge
  have hN := Hilbert.Local.mp (.base htN) ht
  have hnotN : Hilbert.Local T 0 [.neg E,.neg N] (.neg N) :=
   .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  exact Hilbert.Local.explosion E hN hnotN
 exact ⟨.mp (.mp (.logical (.andIntro _ _)) hf.discharge.finish) hb.discharge.finish⟩

theorem chain (T : Sentence → Prop) (A B C : Sentence)
 (hAB : Derivation T (GorbowBooleanTruth.biconditional A B))
 (hBC : Derivation T (GorbowBooleanTruth.biconditional B C)) :
 Nonempty (Derivation T (GorbowBooleanTruth.biconditional A C)) := by
 have hab : Derivation T (.imp A B) := .mp (.logical (.andLeft _ _)) hAB
 have hba : Derivation T (.imp B A) := .mp (.logical (.andRight _ _)) hAB
 have hbc : Derivation T (.imp B C) := .mp (.logical (.andLeft _ _)) hBC
 have hcb : Derivation T (.imp C B) := .mp (.logical (.andRight _ _)) hBC
 exact ⟨.mp (.mp (.logical (.andIntro _ _)) (Hilbert.compose hbc hab)) (Hilbert.compose hba hcb)⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceSelectorClassification.LogicProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceSelectorClassification.LogicProof
