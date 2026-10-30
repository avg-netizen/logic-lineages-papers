module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowDiagonalSentence
public import LogicLineages.ComputabilityKnowledge.GorbowHeaderSubstitutionProof
public import LogicLineages.ComputabilityKnowledge.GorbowFormulaCompositionProof
public import LogicLineages.ComputabilityKnowledge.GorbowProgramDiagramProof
public import LogicLineages.ComputabilityKnowledge.GorbowRegistryRepresentationProof
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryEqualityProof
public import LogicLineages.ComputabilityKnowledge.GorbowDiagonalRegistryProof
public import LogicLineages.ComputabilityKnowledge.GorbowSortedRegistryProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowDiagonalSentenceProof
open GorbowSyntax GorbowStandardInstances GorbowSortedSyntaxCode GorbowTheoryProof
open GorbowDiagonalSentence GorbowFormulaSubstitution GorbowSubstitution GorbowRegistryTuple

private theorem deltaSubstitution {m n : Nat} (σ : Fin m → Term n) (t : Term m) :
    substitute σ (deltaTerm t)=deltaTerm (substitute σ t) := by
  exact congrArg Term.universalFunction (GorbowHeaderSubstitutionProof.headers m n σ 1 2 [t])

private theorem instTheta (φ : Formula 1) (t : Term 0) :
    instantiate (theta φ) t=instantiate φ (deltaTerm t) := by
  unfold instantiate theta
  rw [GorbowFormulaCompositionProof.composition]
  congr 1
  funext i
  have hi : i=0 := Fin.eq_zero i
  subst i
  simp only [deltaSubstitution,substitute,Fin.cases_zero]

theorem literalBody : Comparators.GorbowDiagonalSentence.LiteralBody := by
  intro φ
  exact instTheta φ _

theorem closedEquation : Comparators.GorbowDiagonalSentence.ClosedEquation := by
  intro φ
  let k := formulaCode (theta φ)
  let h := header 1 2 [k]
  let input : Term 0 := headerTerm 1 2 [Term.numeral k]
  obtain ⟨calculation⟩ := (GorbowRegistryRepresentationProof.headerCalculation 1 2 [k]).2.2
  have calc' : Derivation Theory (.equal input (Term.numeral h)) :=
    GorbowTheoryProofProof.coreTree Theory calculation
  obtain ⟨lifted⟩ := GorbowTheoryEqualityProof.termCongruence Theory
    (.universalFunction (.var 0)) input (Term.numeral h) calc'
  have hl : Derivation (n:=0) Theory (.equal (deltaTerm (Term.numeral k))
      (.universalFunction (Term.numeral h))) := by
    simpa only [GorbowClosedEquality.instantiateTerm,substitute,Fin.cases_zero,input,deltaTerm] using lifted
  obtain ⟨equation⟩ := (GorbowProgramDiagramProof.numeralwiseRepresentation
    GorbowSortedRegistry.relationProgram GorbowDiagonalRegistry.functionProgram).2.2
      h (formulaCode (diagonal φ)) |>.mpr (GorbowDiagonalRegistryProof.actualCalibration (theta φ))
  exact GorbowTheoryEqualityProof.transitivity Theory _ _ _ hl equation

theorem fixedPoint : Comparators.GorbowDiagonalSentence.FixedPoint := by
  intro φ
  obtain ⟨p⟩ := closedEquation φ
  have h := GorbowTheoryEqualityProof.formulaEquivalence Theory φ _ _ p
  rw [← literalBody φ] at h
  exact h

theorem originalName : Comparators.GorbowDiagonalSentence.OriginalName := by
  intro n v φ _
  rw [GorbowFormulaCompositionProof.namedSyntax]
  exact fixedPoint (GorbowNamedBinding.selectVariable v φ)

theorem actualTheoryModel : Comparators.GorbowDiagonalSentence.ActualTheoryModel := by
  intro P n φ p
  exact GorbowProgramDiagramProof.theorySoundness
    GorbowSortedRegistry.relationProgram GorbowDiagonalRegistry.functionProgram P n φ p

theorem consistency : Comparators.GorbowDiagonalSentence.Consistency :=
  GorbowProgramDiagramProof.diagramConsistency
    GorbowSortedRegistry.relationProgram GorbowDiagonalRegistry.functionProgram

theorem uniformTheoryProgram : Comparators.GorbowDiagonalSentence.UniformTheoryProgram :=
  GorbowProgramDiagramProof.uniformProgram
    GorbowSortedRegistry.relationProgram GorbowDiagonalRegistry.functionProgram
    GorbowSortedRegistryProof.uniformPrograms.1 GorbowDiagonalRegistryProof.uniformProgram

theorem gorbowDiagonalSentence : Comparators.GorbowDiagonalSentence.Target :=
  ⟨literalBody,closedEquation,fixedPoint,originalName,actualTheoryModel,consistency,uniformTheoryProgram⟩
end LogicLineages.ComputabilityKnowledge.GorbowDiagonalSentenceProof
