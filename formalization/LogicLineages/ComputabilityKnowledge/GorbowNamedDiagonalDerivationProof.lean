module

public import LogicLineages.ComputabilityKnowledge.GorbowNamedDiagonalDerivationTargets
public import LogicLineages.ComputabilityKnowledge.GorbowNamedNumeralCertificatesProof
public import LogicLineages.ComputabilityKnowledge.GorbowFormulaCompositionProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowNamedDiagonalDerivation.Proof
open GorbowSyntax GorbowStandardInstances GorbowSortedSyntaxCode GorbowTheoryProof
open GorbowDiagonalSentence GorbowPRProgram GorbowSubstitution List.Vector
open GorbowNamedDefiningTheory (Theory)

theorem calibratedExistence : Targets.CalibratedExistence := by
  obtain ⟨_,_,pF,pR,hf,hr⟩ := GorbowSourceRegistryPadding.Proof.specificPrograms
  exact ⟨pF,pR,hf,hr⟩

theorem closedEquation : Targets.ClosedEquation := by
  intro pF pR hc phi
  have hn : (1,2) ∈ GorbowSourceRegistryPadding.functionNames := by decide
  have h := GorbowNamedNumeralCertificates.Proof.namedFunctionCalculation pF pR (1,2) hn
    (formulaCode (theta phi) ::ᵥ List.Vector.nil)
  rw [hc.1] at h
  have he := GorbowDiagonalRegistryProof.actualCalibration (theta phi)
  change GorbowSourceRegistryPadding.sourceFunction
    (GorbowNamedNumeralCertificates.inputCode (1,2)
      (formulaCode (theta phi) ::ᵥ List.Vector.nil)) = formulaCode (diagonal phi) at he
  rw [he] at h
  exact h

private theorem deltaSubstitution {m n : Nat} (sigma : Fin m → Term n) (t : Term m) :
    substitute sigma (deltaTerm t) = deltaTerm (substitute sigma t) := by
  exact congrArg Term.universalFunction (GorbowHeaderSubstitutionProof.headers m n sigma 1 2 [t])

private theorem literalBody (phi : Formula 1) :
    diagonal phi = instantiate phi (deltaTerm (Term.numeral (formulaCode (theta phi)))) := by
  change instantiate (theta phi) _ = _
  unfold instantiate theta
  rw [GorbowFormulaCompositionProof.composition]
  congr 1
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  simp only [deltaSubstitution, substitute, Fin.cases_zero]

theorem fixedPoint : Targets.FixedPoint := by
  intro pF pR hc phi
  obtain ⟨h⟩ := closedEquation pF pR hc phi
  have hp := GorbowTheoryEqualityProof.formulaEquivalence (Theory pF pR) phi _ _ h
  rw [← literalBody phi] at hp
  exact hp

theorem originalName : Targets.OriginalName := by
  intro pF pR hc n v phi _
  rw [GorbowFormulaCompositionProof.namedSyntax]
  exact fixedPoint pF pR hc (GorbowNamedBinding.selectVariable v phi)

theorem consistency : Targets.Consistency := by
  intro pF pR hp
  obtain ⟨h⟩ := hp
  let I : Interpretation := ⟨fun _ => False, fun _ => 0, fun _ => False,
    fun _ => False, fun _ _ => False, fun _ => False⟩
  have hs := GorbowNamedDefiningTheory.Proof.theorySoundness pF pR falseEquality h I
  exact Nat.zero_ne_one hs

end LogicLineages.ComputabilityKnowledge.GorbowNamedDiagonalDerivation.Proof
