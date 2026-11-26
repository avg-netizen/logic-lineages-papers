module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.ChosenCommonKnowledgeTransport.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.LogicalSupportProof
public import LogicLineages.ComputabilityKnowledge.GorbowPublishedLobReductionProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.ChosenCommonKnowledgeTransport.ImplicationProof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB
open GorbowSortedSyntaxCode

/-- Certification and selected reflection apply only to a closed ordinary
theorem of the original D, before any temporary local premise is introduced. -/
theorem selectedTheorem (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) (A : Selector) (sigma : Sentence)
    (h : Nonempty (Derivation (D pF pR q c) sigma)) :
    Nonempty (Derivation (D pF pR q c) (everyone A (formulaCode sigma))) := by
  obtain ⟨hp⟩ := GorbowPublishedDCB.Proof.dProofCertification pF pR q c hA sigma h
  obtain ⟨hr⟩ := GorbowPublishedDCB.Proof.selectedReflection pF pR q c hA A sigma
  exact ⟨.mp hr hp⟩

/-- For delta = CK(sigma) -> CK(tau), ordinary deduction proves
Pr_D(delta) -> delta. Both chosen fixed-point instances retain their own
literal formula codes. No theorem rule is applied under a local assumption. -/
theorem preLob (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) (tag : Nat)
    (hFP : GorbowUniformCommonKnowledge.FixedPointFor pF pR q c tag)
    (A : Selector) (sigma tau : Sentence)
    (hImp : Nonempty (Derivation (D pF pR q c) (.imp sigma tau))) :
    Nonempty (Derivation (D pF pR q c)
      (.imp
        (prD pF c (.imp (GorbowUniformCommonKnowledge.closedInstance tag A sigma)
          (GorbowUniformCommonKnowledge.closedInstance tag A tau)))
        (.imp (GorbowUniformCommonKnowledge.closedInstance tag A sigma)
          (GorbowUniformCommonKnowledge.closedInstance tag A tau)))) := by
  let T := D pF pR q c
  let Cs := GorbowUniformCommonKnowledge.closedInstance tag A sigma
  let Ct := GorbowUniformCommonKnowledge.closedInstance tag A tau
  let delta := Formula.imp Cs Ct
  let P := prD pF c delta
  obtain ⟨hSelectedImp⟩ := selectedTheorem pF pR q c hA A (.imp sigma tau) hImp
  obtain ⟨hSigma⟩ := hFP A sigma
  obtain ⟨hTau⟩ := hFP A tau
  obtain ⟨hReflection⟩ := GorbowPublishedDCB.Proof.selectedReflection
    pF pR q c hA A delta
  obtain ⟨hDistribution⟩ := GorbowPublishedDCB.Proof.selectedDistribution
    pF pR q c hA A sigma tau
  obtain ⟨hSelfDistribution⟩ := GorbowPublishedDCB.Proof.selectedDistribution
    pF pR q c hA A Cs Ct
  have hCs : Hilbert.Local T 0 [Cs, P] Cs := .hypothesis List.mem_cons_self
  have hP : Hilbert.Local T 0 [Cs, P] P :=
    .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  have hParts : Hilbert.Local T 0 [Cs, P]
      (.conj (everyone A (formulaCode sigma)) (everyone A (formulaCode Cs))) :=
    .mp (.base (.mp (.logical (.andLeft _ _)) hSigma)) hCs
  have hESigma : Hilbert.Local T 0 [Cs, P] (everyone A (formulaCode sigma)) :=
    .mp (.base (.logical (.andLeft _ _))) hParts
  have hECs : Hilbert.Local T 0 [Cs, P] (everyone A (formulaCode Cs)) :=
    .mp (.base (.logical (.andRight _ _))) hParts
  have hETau : Hilbert.Local T 0 [Cs, P] (everyone A (formulaCode tau)) :=
    .mp (.mp (.base hDistribution) (.base hSelectedImp)) hESigma
  have hEDelta : Hilbert.Local T 0 [Cs, P] (everyone A (formulaCode delta)) :=
    .mp (.base hReflection) hP
  have hECt : Hilbert.Local T 0 [Cs, P] (everyone A (formulaCode Ct)) :=
    .mp (.mp (.base hSelfDistribution) hEDelta) hECs
  have hTargetParts : Hilbert.Local T 0 [Cs, P]
      (.conj (everyone A (formulaCode tau)) (everyone A (formulaCode Ct))) :=
    .mp (.mp (.base (.logical (.andIntro _ _))) hETau) hECt
  have hCt : Hilbert.Local T 0 [Cs, P] Ct :=
    .mp (.base (.mp (.logical (.andRight _ _)) hTau)) hTargetParts
  exact ⟨Hilbert.Local.finish
    (Hilbert.Local.discharge (Hilbert.Local.discharge hCt))⟩

/-- The existing source Lob reduction consumes the original internal HB
schemas at this same tuple; no fresh selected presentation is introduced. -/
theorem implicationTransport : Targets.ImplicationTransport := by
  intro pF pR q c hA tag hFP h2 h3 A sigma tau hImp
  exact GorbowPublishedLobReduction.Proof.globalLobReduction pF pR q c hA h2 h3
    (.imp (GorbowUniformCommonKnowledge.closedInstance tag A sigma)
      (GorbowUniformCommonKnowledge.closedInstance tag A tau))
    (preLob pF pR q c hA tag hFP A sigma tau hImp)

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.ChosenCommonKnowledgeTransport.ImplicationProof

#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.ChosenCommonKnowledgeTransport.ImplicationProof
