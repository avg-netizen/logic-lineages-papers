module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceCalibrationProof
open Source GammaGuardedSource GammaGuardCalibration GammaGuardCalibrationProof
open GuardedSourceCalibrationProof InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem evalAtInput {m : Nat} (p : Program 1) (i : Fin m) (v : List.Vector Nat m) :
    evaluate (atInput p i) v = evaluate p (List.Vector.ofFn ![v.get i]) := by
  rw [atInput,evalComposeOne]
  rfl

theorem evalSameGamma {m : Nat} (gamma : Program 1) (i j : Fin m) (v : List.Vector Nat m) :
    evaluate (sameGamma gamma i j) v =
      if evaluate gamma (List.Vector.ofFn ![v.get i]) =
        evaluate gamma (List.Vector.ofFn ![v.get j]) then 1 else 0 := by
  rw [sameGamma,evalComposeTwo,evalAtInput,evalAtInput,evalEquality]

theorem gammaCalibration (gamma : Program 1)
    (hg : ∀ v, evaluate gamma v = gammaValue v) (x : Nat) :
    evaluate gamma (List.Vector.ofFn ![x]) = gammaCode x := by
  rw [hg]
  rfl

theorem validCalibration (valid : Program 1)
    (hv : ∀ v, evaluate valid v = objectValid (v.get 0)) (x : Nat) :
    evaluate valid (List.Vector.ofFn ![x]) = objectValid x := by
  rw [hv]
  rfl

theorem baseTypedCalibration (n : Nat) (arity : Fin n → Nat)
    (typed : Program 3) (valid : Program 1)
    (ht : ∀ v, evaluate typed v = JointGammaTyped.typedValue n arity v)
    (hv : ∀ v, evaluate valid v = objectValid (v.get 0)) (v : List.Vector Nat 3) :
    evaluate (baseTyped typed valid) v = JointGammaTyped.typedValue n arity v := by
  rw [baseTyped,actualConjunctionEvaluation,ht,evalAtInput,validCalibration valid hv]
  rcases actualTypedRange n arity v with hz | ho
  · simp only [hz,Nat.zero_ne_one,false_and,ite_false]
  · have hvalid := actualTypedValid n arity (v.get 0) (v.get 1) (v.get 2)
        (by simpa only [vectorThree] using ho)
    simp only [ho,hvalid,and_self,ite_true]

theorem basePositiveCalibration (n : Nat) (arity : Fin n → Nat)
    (positive : Program 4) (gamma : Program 1)
    (hp : ∀ v, evaluate positive v = ContextUniform.positiveValue n arity v)
    (hg : ∀ v, evaluate gamma v = gammaValue v) (v : List.Vector Nat 4) :
    evaluate (basePositive positive gamma) v = ContextUniform.positiveValue n arity v := by
  rw [basePositive,actualConjunctionEvaluation,hp,evalSameGamma,
    gammaCalibration gamma hg,gammaCalibration gamma hg]
  rcases PositiveTypedCalibrationProof.actualPositiveRange n arity v with hz | ho
  · simp only [hz,Nat.zero_ne_one,false_and,ite_false]
  · have he := actualPositiveGamma n arity (v.get 0) (v.get 1) (v.get 2) (v.get 3)
        (by simpa only [vectorFour] using ho)
    simp only [ho,he,and_self,ite_true]

theorem vectorTwo (v : List.Vector Nat 2) : List.Vector.ofFn ![v.get 0,v.get 1] = v := by
  apply List.Vector.ext
  intro i
  exact Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)) i

theorem guardCalibration (valid gamma : Program 1)
    (hv : ∀ v, evaluate valid v = objectValid (v.get 0))
    (hg : ∀ v, evaluate gamma v = gammaValue v) (v : List.Vector Nat 2) :
    evaluate (guard valid gamma) v = JointGammaDomain.guardValue v := by
  rw [GammaGuardedSource.guard,actualConjunctionEvaluation,actualConjunctionEvaluation,evalAtInput,evalAtInput,
    validCalibration valid hv,validCalibration valid hv,evalSameGamma,
    gammaCalibration gamma hg,gammaCalibration gamma hg]
  have hc := actualGuardCalibration (v.get 0) (v.get 1)
  rw [vectorTwo] at hc
  rcases actualGuardRange v with hz | ho
  · have hn : ¬ (objectValid (v.get 0) = 1 ∧ objectValid (v.get 1) = 1 ∧
        gammaCode (v.get 0) = gammaCode (v.get 1)) := by
      intro h
      have := hc.mpr h
      rw [hz] at this
      exact Nat.zero_ne_one this
    by_cases hx : objectValid (v.get 0) = 1
    · by_cases hu : objectValid (v.get 1) = 1
      · have he : gammaCode (v.get 0) ≠ gammaCode (v.get 1) := fun h => hn ⟨hx,hu,h⟩
        simp only [hz,hx,hu,if_neg he,Nat.zero_ne_one,eq_self_iff_true,true_and,ite_false]
      · simp only [hz,hx,hu,eq_self_iff_true,true_and,false_and,ite_false,Nat.zero_ne_one]
    · simp only [hz,hx,false_and,ite_false]
  · obtain ⟨hx,hu,he⟩ := hc.mp ho
    simp only [ho,hx,hu,he,eq_self_iff_true,and_self,ite_true]

theorem actualBaseCalibration : GammaGuardedSourceTargets.ActualBaseCalibration := by
  intro n arity oldSource oldComp valid gamma hs hc hv hg
  constructor
  · exact ⟨hs.1,hs.2.1,basePositiveCalibration n arity oldSource.positive gamma hs.2.2.1 hg,hs.2.2.2⟩
  · exact ⟨baseTypedCalibration n arity oldComp.typed valid hc.1 hv,
      guardCalibration valid gamma hv hg,hc.2.2⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceCalibrationProof
