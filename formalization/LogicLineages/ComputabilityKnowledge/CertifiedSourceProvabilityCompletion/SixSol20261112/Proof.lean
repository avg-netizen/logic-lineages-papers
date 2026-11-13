module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.LogicalSupportProof
public import LogicLineages.ComputabilityKnowledge.GorbowUniformCommonKnowledgeProof
public import LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.BaseProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRNegativeNumeralsProof

@[expose] public section
/-! The printed corollary's contradiction step, in the actual source D.
The concrete installed retained-parameter CK equation supplies its forward
implication. Its reverse implication uses only PA's refutation of b, actual
theorem certification/reflection and selected distribution. Necessitation is
applied exclusively to a completed theorem b -> CK_A(#b), before introducing
the local assumption E_A(b). Actual internal HB2/HB3 remain separate. -/
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Proof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB
open GorbowSortedSyntaxCode

theorem installedContradictionReduction : Targets.InstalledContradictionReduction := by
  intro pF pR q c tag p hA hCode hInstall A
  let T := D pF pR q c
  let C := GorbowUniformCommonKnowledge.closedInstance tag A falseEquality
  let E := everyone A (formulaCode falseEquality)
  let EC := everyone A (formulaCode C)
  obtain ⟨hfixed⟩ := GorbowUniformCommonKnowledge.Proof.closedFixedPoint
    pF pR q c tag p hA hCode hInstall A falseEquality
  have hparts : Derivation T (.imp C (.conj E EC)) :=
    .mp (.logical (.andLeft _ _)) hfixed
  have hforward : Derivation T (.imp C E) :=
    Hilbert.compose (.logical (.andLeft E EC)) hparts
  have hreturn : Derivation T (.imp (.conj E EC) C) :=
    .mp (.logical (.andRight _ _)) hfixed
  obtain ⟨hnotb⟩ := GorbowPRNegativeNumerals.Proof.unequalNumerals T 0 1 (by decide)
  have hbc : Derivation T (.imp falseEquality C) :=
    Hilbert.Local.finish (Hilbert.Local.discharge
      (Hilbert.Local.explosion C (.hypothesis List.mem_cons_self) (.base hnotb)))
  obtain ⟨hcert⟩ := GorbowPublishedDCB.Proof.dProofCertification pF pR q c hA
    (.imp falseEquality C) ⟨hbc⟩
  obtain ⟨hreflect⟩ := GorbowPublishedDCB.Proof.selectedReflection pF pR q c hA
    A (.imp falseEquality C)
  have hecImp : Derivation T (everyone A (formulaCode (.imp falseEquality C))) :=
    .mp hreflect hcert
  obtain ⟨hdistribution⟩ := GorbowPublishedDCB.Proof.selectedDistribution
    pF pR q c hA A falseEquality C
  have hec : Derivation T (.imp E EC) := .mp hdistribution hecImp
  have he : Hilbert.Local T 0 [E] E := .hypothesis List.mem_cons_self
  have hecLocal : Hilbert.Local T 0 [E] EC := .mp (.base hec) he
  have hboth : Hilbert.Local T 0 [E] (.conj E EC) :=
    .mp (.mp (.base (.logical (.andIntro E EC))) he) hecLocal
  have hbackward : Derivation T (.imp E C) :=
    Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.base hreturn) hboth))
  exact ⟨.mp (.mp (.logical (.andIntro _ _)) hforward) hbackward⟩

theorem sameSourceContradictionReduction : Targets.SameSourceContradictionReduction := by
  obtain ⟨pF, pR, q, c, tag, p, hA, hCode, hInstall⟩ :=
    GorbowUniformCommonKnowledge.Proof.enrichedParameters
  refine ⟨pF, pR, q, c, tag, p, hA, ?_, hCode, hInstall, ?_, ?_⟩
  · exact SourceBaseCompletion.Proof.actualSyntaxAdequacy pF pR q c hA
  · exact GorbowUniformCommonKnowledge.Proof.closedFixedPoint pF pR q c tag p hA hCode hInstall
  · exact installedContradictionReduction pF pR q c tag p hA hCode hInstall

/-- Explicit remaining dependency, not a proof of either original target. -/
theorem commonBeliefFromCollapse : Targets.CommonBeliefFromCollapse := by
  rintro ⟨pF, pR, q, c, tag, p, hA, hSyntax, hCode, hInstall, hFixed, hCollapse⟩
  refine ⟨pF, pR, q, c, tag, p, hA, hSyntax, hCode, hInstall, hFixed, ?_⟩
  intro A
  obtain ⟨hc⟩ := hCollapse A
  obtain ⟨hk⟩ := installedContradictionReduction pF pR q c tag p hA hCode hInstall A
  have hce : Derivation (D pF pR q c) (.imp (sourceC tag A)
      (everyone A (formulaCode falseEquality))) :=
    .mp (.logical (.andLeft _ _)) hc
  have hec : Derivation (D pF pR q c) (.imp (everyone A (formulaCode falseEquality))
      (sourceC tag A)) := .mp (.logical (.andRight _ _)) hc
  have hke : Derivation (D pF pR q c)
      (.imp (GorbowUniformCommonKnowledge.closedInstance tag A falseEquality)
        (everyone A (formulaCode falseEquality))) :=
    .mp (.logical (.andLeft _ _)) hk
  have hek : Derivation (D pF pR q c)
      (.imp (everyone A (formulaCode falseEquality))
        (GorbowUniformCommonKnowledge.closedInstance tag A falseEquality)) :=
    .mp (.logical (.andRight _ _)) hk
  exact ⟨.mp (.mp (.logical (.andIntro _ _)) (Hilbert.compose hek hce))
    (Hilbert.compose hec hke)⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Proof
