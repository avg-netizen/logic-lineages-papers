module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.EquationsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.StepProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPRDefiningEquations
open GorbowPRChildTags List.Vector
open NamedArithmeticGraph

theorem openStep : Targets.OpenStep := by
  intro n p tag q0 htag ctx index fuel context formula cert
  let T := GorbowPRNumeralCalculation.Theory p
  let accTag := tag+1
  let st := accTag+stepTag (base q0)
  let ot := st+1
  let retained := index ::ᵥ context ::ᵥ formula ::ᵥ cert ::ᵥ nil
  let previous := call accTag (fuel ::ᵥ retained)
  let args := fuel ::ᵥ previous ::ᵥ retained
  let current := call (st+argumentTag leftOr (stepArguments q0) 1) args
  have ha : (nodes p)[accTag]? = some ⟨5,accumulator q0⟩ :=
    Equations.functionChild p tag (accumulator q0) outerArguments htag
  have hs : (nodes p)[st]? = some ⟨6,step q0⟩ :=
    Equations.recursionStepChild p accTag (base q0) (step q0) ha
  have ho : (nodes p)[ot]? = some ⟨2,leftOr⟩ :=
    Equations.functionChild p st leftOr (stepArguments q0) hs
  obtain ⟨hroot⟩ := Equations.verifierEquation p tag q0 htag index fuel context formula cert
  obtain ⟨hnext⟩ := Equations.verifierEquation p tag q0 htag index (.succ fuel) context formula cert
  obtain ⟨hrec⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation
    n p accTag 4 (base q0) (step q0) ha ctx fuel retained
  have hargs : ∀ i : Fin 2, Nonempty (Derivation T
      (.equal (call (st+argumentTag leftOr (stepArguments q0) i) args)
        ((previous ::ᵥ current ::ᵥ nil).get i))) := by
    intro i
    cases i using Fin.cases with
    | zero =>
        have hp := Equations.argumentChild p st leftOr (stepArguments q0) hs 0
        exact Equations.projection p (st+argumentTag leftOr (stepArguments q0) 0)
          (1 : Fin 6) hp args
    | succ i =>
        have hi : i = 0 := Fin.eq_zero i
        subst i
        exact ⟨.logical (.reflexive current)⟩
  obtain ⟨hstep⟩ := Equations.compositionValues p st leftOr (stepArguments q0) hs
    args (previous ::ᵥ current ::ᵥ nil) hargs
  have hfull : Derivation T (.equal
      (call tag (inputs index (.succ fuel) context formula cert))
      (call ot (previous ::ᵥ current ::ᵥ nil))) :=
    Logic.trans _ _ _ hnext (Logic.trans _ _ _ hrec hstep)
  obtain ⟨hor⟩ := Equations.orOneRule p ot ho previous current
  have hfirst : Derivation T (.imp (success tag index fuel context formula cert)
      (.equal previous (Term.numeral 1))) := Logic.oneTransport _ _ hroot
  have hlast : Derivation T (.imp (.equal (call ot (previous ::ᵥ current ::ᵥ nil)) (Term.numeral 1))
      (success tag index (.succ fuel) context formula cert)) :=
    Logic.oneTransport _ _ (Support.equalitySymmetry _ _ hfull)
  exact ⟨Hilbert.compose hlast (Hilbert.compose hor hfirst)⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.StepProof
