module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCommonKnowledgeCounterexample.CollapseProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCommonKnowledgeCounterexample.KTTransportProof
public import LogicLineages.ComputabilityKnowledge.GorbowPublishedKTStatementChecks
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCommonKnowledgeCounterexample.Proof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB

/-- The source KT proves the negation at the displayed sentence's actual
CK code. The ordinary collapse is lifted into KT; its theta theorem is
combined by modus ponens, never necessitated under a temporary assumption. -/
theorem literalNegation (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) (tag : Nat)
    (hFP : GorbowUniformCommonKnowledge.FixedPointFor pF pR q c tag)
    (h2 : ∀ sigma tau : Sentence, Nonempty (Derivation (D pF pR q c)
      (GorbowPublishedLobReduction.hb2 pF c sigma tau)))
    (h3 : ∀ sigma : Sentence, Nonempty (Derivation (D pF pR q c)
      (GorbowPublishedLobReduction.hb3 pF c sigma))) :
    Nonempty (GorbowPublishedKT.Proof false pF pR q c
      (.neg (GorbowUniformCommonKnowledge.closedInstance tag topSelector literalTheta))) := by
  let T := GorbowPublishedKT.Axiom false pF pR q c
  let C := GorbowUniformCommonKnowledge.closedInstance tag topSelector literalTheta
  let E := everyone topSelector (GorbowSortedSyntaxCode.formulaCode falseEquality)
  obtain ⟨hCollapse⟩ := GorbowTheoryProofProof.monotonicity (D pF pR q c) T
    (fun sigma hs => GorbowPublishedKT.Axiom.d sigma hs) 0 _
    (CollapseProof.literalCollapse pF pR q c hA tag hFP h2 h3)
  have hCE : GorbowPublishedKT.Proof false pF pR q c (.imp C E) :=
    .ordinary (.mp (.logical (.andLeft _ _)) hCollapse)
  obtain ⟨hTheta⟩ := CertifiedSourceProvabilityCompletion.Proof.directTheta pF pR q c hA
  have hLiftTheta : GorbowPublishedKT.Proof false pF pR q c
      (.imp C (.imp E falseEquality)) :=
    .mp (.ordinary (.logical (.k (.imp E falseEquality) C))) hTheta
  have hCB : GorbowPublishedKT.Proof false pF pR q c (.imp C falseEquality) :=
    .mp (.mp (.ordinary (.logical (.s C E falseEquality))) hLiftTheta) hCE
  obtain ⟨hNotFalse⟩ := GorbowPRNegativeNumerals.Proof.unequalNumerals T 0 1 (by decide)
  obtain ⟨hRefute⟩ := KTTransportProof.implicationToNegation T C falseEquality hNotFalse
  exact ⟨.mp (.ordinary hRefute) hCB⟩

/-- Both original theories retain the literal theorem and refutation.
Nonprovability uses the already proved revision consistency at the SAME
Actual tuple, including its original optional-UBF case. -/
theorem literalCounterexample : Targets.LiteralCounterexample := by
  intro pF pR q c hA tag hFP h2 h3 withUBF
  let C := GorbowUniformCommonKnowledge.closedInstance tag topSelector literalTheta
  obtain ⟨hTheta⟩ := LiteralProof.literalDirectTheta pF pR q c hA
  obtain ⟨hNeg⟩ := literalNegation pF pR q c hA tag hFP h2 h3
  obtain ⟨hNegFlag⟩ := KTTransportProof.proofInclusion pF pR q c withUBF hNeg
  refine ⟨KTTransportProof.proofInclusion pF pR q c withUBF hTheta, ⟨hNegFlag⟩, ?_, ?_⟩
  · intro r
    obtain ⟨hIteration⟩ := LiteralProof.literalFiniteIteration pF pR q c hA r
    exact KTTransportProof.proofInclusion pF pR q c withUBF hIteration
  · rintro ⟨hC⟩
    have hLiftNeg : GorbowPublishedKT.Proof withUBF pF pR q c
        (.imp (.neg falseEquality) (.neg C)) :=
      .mp (.ordinary (.logical (.k (.neg C) (.neg falseEquality)))) hNegFlag
    have hCFalse : GorbowPublishedKT.Proof withUBF pF pR q c (.imp C falseEquality) :=
      .mp (.ordinary (.logical (.classicalContraposition falseEquality C))) hLiftNeg
    exact GorbowPublishedKT.StatementChecks.consistency pF pR q c hA withUBF
      ⟨.mp hCFalse hC⟩

/-- Destruct exactly one original selected presentation. Its source, CK
registry, full fixed-point family and internal-HB witnesses are all retained. -/
theorem fromSelectedPresentation : Targets.FromSelectedPresentation := by
  rintro ⟨pF, pR, q, c, tag, p, hA, hSyntax, hCode, hInstall, hFP, h2, h3⟩
  exact ⟨pF, pR, q, c, tag, p, hA, hSyntax, hCode, hInstall, hFP, h2, h3,
    CollapseProof.literalCollapse pF pR q c hA tag hFP h2 h3,
    literalCounterexample pF pR q c hA tag hFP h2 h3⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCommonKnowledgeCounterexample.Proof

#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCommonKnowledgeCounterexample.Proof
