module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.CollapseReductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceContradictionCorollaryV2.ConsumerProof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB
open GorbowSortedSyntaxCode
theorem contradictionImplies (T : Sentence → Prop) (sigma : Sentence) :
 Nonempty (Derivation T (.imp falseEquality sigma)) := by
 obtain ⟨hn⟩ := GorbowPRNegativeNumerals.Proof.unequalNumerals T 0 1 (by decide)
 have h : Hilbert.Local T 0 [falseEquality] sigma :=
  Hilbert.Local.explosion sigma (.hypothesis List.mem_cons_self) (.base hn)
 exact ⟨h.discharge.finish⟩

/-- Selection is applied only to a completed actual theorem, never to the
local E(b) assumption used later in the propositional assembly. -/
theorem selectedTheorem (pF pR : Program 1) (q : Program 5) (c : Code)
 (hA : Actual pF pR q c) (A : Selector) (sigma : Sentence)
 (h : Nonempty (Derivation (D pF pR q c) sigma)) :
 Nonempty (Derivation (D pF pR q c) (everyone A (formulaCode sigma))) := by
 obtain ⟨hp⟩ := GorbowPublishedDCB.Proof.dProofCertification pF pR q c hA sigma h
 obtain ⟨hr⟩ := GorbowPublishedDCB.Proof.selectedReflection pF pR q c hA A sigma
 exact ⟨.mp hr hp⟩

theorem corollary (pF pR : Program 1) (q : Program 5) (c : Code) (tag : Nat)
 (hA : Actual pF pR q c) (hFP : GorbowUniformCommonKnowledge.FixedPointFor pF pR q c tag)
 (A : Selector)
 (hCollapse : Nonempty (Derivation (D pF pR q c)
  (GorbowBooleanTruth.biconditional (sourceC tag A) (everyone A (formulaCode falseEquality))))) :
 Nonempty (Derivation (D pF pR q c) (GorbowBooleanTruth.biconditional (sourceC tag A)
  (GorbowUniformCommonKnowledge.closedInstance tag A falseEquality))) := by
 let T := D pF pR q c
 let B := GorbowUniformCommonKnowledge.closedInstance tag A falseEquality
 let E := everyone A (formulaCode falseEquality)
 let EB := everyone A (formulaCode B)
 obtain ⟨hfixed⟩ := hFP A falseEquality
 have hforward : Derivation T (.imp B E) :=
  Hilbert.compose (.logical (.andLeft E EB)) (.mp (.logical (.andLeft _ _)) hfixed)
 obtain ⟨hbc⟩ := contradictionImplies T B
 obtain ⟨hebc⟩ := selectedTheorem pF pR q c hA A (.imp falseEquality B) ⟨hbc⟩
 obtain ⟨hd⟩ := GorbowPublishedDCB.Proof.selectedDistribution pF pR q c hA A falseEquality B
 have heToEB : Derivation T (.imp E EB) := .mp hd hebc
 have he : Hilbert.Local T 0 [E] E := .hypothesis List.mem_cons_self
 have parts : Hilbert.Local T 0 [E] (.conj E EB) :=
  .mp (.mp (.base (.logical (.andIntro E EB))) he) (.mp (.base heToEB) he)
 have hback : Derivation T (.imp E B) :=
  (Hilbert.Local.mp (.base (.mp (.logical (.andRight _ _)) hfixed)) parts).discharge.finish
 obtain ⟨hc⟩ := hCollapse
 have hCE : Derivation T (.imp (sourceC tag A) E) := .mp (.logical (.andLeft _ _)) hc
 have hEC : Derivation T (.imp E (sourceC tag A)) := .mp (.logical (.andRight _ _)) hc
 exact ⟨.mp (.mp (.logical (.andIntro _ _)) (Hilbert.compose hback hCE))
  (Hilbert.compose hEC hforward)⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceContradictionCorollaryV2.ConsumerProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceContradictionCorollaryV2.ConsumerProof
