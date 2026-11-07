module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationDomainTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaDomainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationDomainProgramProof
open Source ApplicationDomain
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

attribute [local irreducible] Primrec

theorem arrowPrimitive : Primrec arrowValue := by
  have hg (i : Fin 2) : Primrec (fun v : List.Vector Nat 2 => v.get i) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const i)
  exact Primrec.nat_add.comp (Primrec.const 1) (Primrec₂.natPair.comp (hg 0) (hg 1))

theorem actualActivationCalibration : ApplicationDomainTargets.ActualActivationCalibration := by
  intro n arity v
  by_cases h : active n arity v <;> simp [activationValue,h]

theorem evaluateComposition2 {n : Nat} (p : Program 2) (q r : Program n)
    (v : List.Vector Nat n) :
    evaluate (.composition p ![q,r]) v =
      evaluate p (List.Vector.ofFn ![evaluate q v,evaluate r v]) := by
  change evaluate p _ = evaluate p _
  congr 1

theorem evaluateComposition3 {n : Nat} (p : Program 3) (q r s : Program n)
    (v : List.Vector Nat n) :
    evaluate (.composition p ![q,r,s]) v =
      evaluate p (List.Vector.ofFn ![evaluate q v,evaluate r v,evaluate s v]) := by
  change evaluate p _ = evaluate p _
  congr 1

theorem actualExplicitActivation : ApplicationDomainTargets.ActualExplicitActivation := by
  intro n arity window typed guard arrow hw ht hg hr v
  unfold activation
  rw [InternalAcceptanceCalibrationProof.actualConjunctionEvaluation,
    InternalAcceptanceCalibrationProof.actualConjunctionEvaluation,
    InternalAcceptanceCalibrationProof.actualConjunctionEvaluation]
  simp only [evaluateComposition2,evaluateComposition3]
  simp only [evaluate,hw,ht,hg,hr,GuardCalibration.validWindowValue,arrowValue,
    List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one]
  unfold activationValue active
  split_ifs <;> simp_all

theorem actualActivationProgram : ApplicationDomainTargets.ActualActivationProgram := by
  intro n arity
  obtain ⟨window,hw⟩ := GuardCalibrationProof.actualValidWindowProgram n
  obtain ⟨typed,ht⟩ := Proof.allPrimitiveFunctions 3 (JointGammaTyped.typedValue n arity)
    (JointGammaTypedPrimitiveProof.actualObjectTypedPrimitive n arity)
  obtain ⟨guard,hg⟩ := Proof.allPrimitiveFunctions 2 JointGammaDomain.guardValue
    JointGammaDomainProof.actualGuardPrimitive
  obtain ⟨arrow,hr⟩ := Proof.allPrimitiveFunctions 2 arrowValue arrowPrimitive
  exact ⟨window,typed,guard,arrow,hw,ht,hg,hr,
    actualExplicitActivation n arity window typed guard arrow hw ht hg hr⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationDomainProgramProof
