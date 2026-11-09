module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.CollapseTargets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.LogicalSupportProof
public import LogicLineages.ComputabilityKnowledge.GorbowPublishedLobReductionProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRNegativeNumeralsProof

@[expose] public section
/-! The finite source-collapse consumer, with exactly the three needed local
HB derivations left explicit. It does NOT construct those internal arithmetic
derivations or accept a whole source-collapse theorem. -/
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.CollapseProof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB
open GorbowSortedSyntaxCode

private theorem selectedTheorem (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) (A : Selector) (sigma : Sentence)
    (h : Nonempty (Derivation (D pF pR q c) sigma)) :
    Nonempty (Derivation (D pF pR q c) (everyone A (formulaCode sigma))) := by
  obtain ⟨hp⟩ := GorbowPublishedDCB.Proof.dProofCertification pF pR q c hA sigma h
  obtain ⟨hr⟩ := GorbowPublishedDCB.Proof.selectedReflection pF pR q c hA A sigma
  exact ⟨.mp hr hp⟩

private theorem contradictionImplies (T : Sentence → Prop) (sigma : Sentence) :
    Nonempty (Derivation T (.imp falseEquality sigma)) := by
  obtain ⟨hn⟩ := GorbowPRNegativeNumerals.Proof.unequalNumerals T 0 1 (by decide)
  have h : Hilbert.Local T 0 [falseEquality] sigma :=
    Hilbert.Local.explosion sigma (.hypothesis List.mem_cons_self) (.base hn)
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge h)⟩

private theorem preLob (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) (tag : Nat)
    (hFP : GorbowUniformCommonKnowledge.FixedPointFor pF pR q c tag) (A : Selector) :
    Nonempty (Derivation (D pF pR q c)
      (.imp (prD pF c (collapseDelta tag A)) (collapseDelta tag A))) := by
  let T := D pF pR q c
  let C := sourceC tag A
  let E := everyone A (formulaCode falseEquality)
  let theta := selectorTheta A
  let delta := collapseDelta tag A
  let P := prD pF c delta
  let B1 := GorbowClosedDeduction.extend T P
  let B := GorbowClosedDeduction.extend B1 C
  obtain ⟨hf⟩ := hFP A theta
  obtain ⟨hr⟩ := GorbowPublishedDCB.Proof.selectedReflection pF pR q c hA A delta
  obtain ⟨hd1⟩ := GorbowPublishedDCB.Proof.selectedDistribution pF pR q c hA A C E
  obtain ⟨hd2⟩ := GorbowPublishedDCB.Proof.selectedDistribution pF pR q c hA A E falseEquality
  have embed : ∀ s, T s → B s := fun _ h => Or.inl (Or.inl h)
  obtain ⟨hfB⟩ := GorbowTheoryProofProof.monotonicity T B embed 0 _ ⟨hf⟩
  obtain ⟨hrB⟩ := GorbowTheoryProofProof.monotonicity T B embed 0 _ ⟨hr⟩
  obtain ⟨hd1B⟩ := GorbowTheoryProofProof.monotonicity T B embed 0 _ ⟨hd1⟩
  obtain ⟨hd2B⟩ := GorbowTheoryProofProof.monotonicity T B embed 0 _ ⟨hd2⟩
  have hp : Derivation B P := by
    have h := Derivation.axiom (A := B) (n := 0) P (Or.inl (Or.inr rfl))
    rw [GorbowClosedDeductionProof.closedSyntax.1] at h
    exact h
  have hc : Derivation B C := by
    have h := Derivation.axiom (A := B) (n := 0) C (Or.inr rfl)
    rw [GorbowClosedDeductionProof.closedSyntax.1] at h
    exact h
  have hcparts : Derivation B
      (.conj (everyone A (formulaCode theta)) (everyone A (formulaCode C))) :=
    .mp (.mp (.logical (.andLeft _ _)) hfB) hc
  have htheta : Derivation B (everyone A (formulaCode theta)) :=
    .mp (.logical (.andLeft _ _)) hcparts
  have hec : Derivation B (everyone A (formulaCode C)) :=
    .mp (.logical (.andRight _ _)) hcparts
  have hedelta : Derivation B (everyone A (formulaCode delta)) := .mp hrB hp
  have hee : Derivation B (everyone A (formulaCode E)) := .mp (.mp hd1B hedelta) hec
  have he : Derivation B E := .mp (.mp hd2B htheta) hee
  obtain ⟨hdelta⟩ := GorbowClosedDeductionProof.deduction B1 C 0 E he
  rw [GorbowClosedDeductionProof.closedSyntax.1] at hdelta
  obtain ⟨h⟩ := GorbowClosedDeductionProof.deduction T P 0 delta hdelta
  exact ⟨by simpa only [GorbowClosedDeductionProof.closedSyntax.1] using h⟩

private theorem reverseCollapse (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) (tag : Nat)
    (hFP : GorbowUniformCommonKnowledge.FixedPointFor pF pR q c tag) (A : Selector) :
    Nonempty (Derivation (D pF pR q c)
      (.imp (everyone A (formulaCode falseEquality)) (sourceC tag A))) := by
  let T := D pF pR q c
  let C := sourceC tag A
  let E := everyone A (formulaCode falseEquality)
  let theta := selectorTheta A
  obtain ⟨hbt⟩ := contradictionImplies T theta
  obtain ⟨hbc⟩ := contradictionImplies T C
  obtain ⟨hebt⟩ := selectedTheorem pF pR q c hA A (.imp falseEquality theta) ⟨hbt⟩
  obtain ⟨hebc⟩ := selectedTheorem pF pR q c hA A (.imp falseEquality C) ⟨hbc⟩
  obtain ⟨hdt⟩ := GorbowPublishedDCB.Proof.selectedDistribution pF pR q c hA A falseEquality theta
  obtain ⟨hdc⟩ := GorbowPublishedDCB.Proof.selectedDistribution pF pR q c hA A falseEquality C
  have ht : Derivation T (.imp E (everyone A (formulaCode theta))) := .mp hdt hebt
  have hc : Derivation T (.imp E (everyone A (formulaCode C))) := .mp hdc hebc
  obtain ⟨hfixed⟩ := hFP A theta
  have hback : Derivation T (.imp
      (.conj (everyone A (formulaCode theta)) (everyone A (formulaCode C))) C) :=
    .mp (.logical (.andRight _ _)) hfixed
  have he : Hilbert.Local T 0 [E] E := .hypothesis List.mem_cons_self
  have hparts : Hilbert.Local T 0 [E]
      (.conj (everyone A (formulaCode theta)) (everyone A (formulaCode C))) :=
    .mp (.mp (.base (.logical (.andIntro _ _))) (.mp (.base ht) he)) (.mp (.base hc) he)
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.base hback) hparts))⟩

theorem localCollapseReduction : CollapseTargets.LocalCollapseReduction := by
  intro pF pR q c hA tag hFP A h1 h2 h3
  obtain ⟨hp⟩ := preLob pF pR q c hA tag hFP A
  obtain ⟨hf⟩ := GorbowPublishedLobReduction.Proof.localLobReduction
    pF pR q c hA (collapseDelta tag A) h1 h2 h3 ⟨hp⟩
  obtain ⟨hb⟩ := reverseCollapse pF pR q c hA tag hFP A
  exact ⟨.mp (.mp (.logical (.andIntro _ _)) hf) hb⟩

/-- Pure assembly, with the missing selected internal-HB existence still
explicit on the left. This is not a proof of SourceCollapse alone. -/
theorem sourceCollapseFromSelectedLocalHB :
    CollapseTargets.SelectedLocalHB → CollapseTargets.SourceCollapse := by
  rintro ⟨pF, pR, q, c, tag, p, hA, hS, hCode, hInstall, hFP, hHB⟩
  refine ⟨pF, pR, q, c, tag, p, hA, hS, hCode, hInstall, hFP, ?_⟩
  intro A
  exact localCollapseReduction pF pR q c hA tag hFP A
    (hHB A).1 (hHB A).2.1 (hHB A).2.2

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.CollapseProof
