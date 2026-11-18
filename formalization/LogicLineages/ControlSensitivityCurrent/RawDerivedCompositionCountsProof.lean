module
public import LogicLineages.ControlSensitivityCurrent.RawDerivedCompositionSuccessProof
public import LogicLineages.ControlSensitivityCurrent.RawCheckedCompositionCountsProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.DerivedComposition
open LogicLineages.OrdinalComparison.Source
open CheckedComposition Operations

theorem detector_sizes (a b : Code) :
    (detectorLeftRaw a b).2.1.length=2*(a.2.1.length+b.2.1.length)+6 ∧
    (detectorRightRaw a b).2.1.length=2*(a.2.1.length+b.2.1.length)+6 := by
  simp only [detectorLeftRaw,detectorRightRaw,eraser_size]
  omega

theorem aggregate_sizes (context : List Nat) (es : List (Code × Code)) :
    (aggregateRaw context es).1.2.1.length=rawWeight es ∧
    (aggregateRaw context es).2.2.1.length=rawWeight es := by
  induction es with
  | nil => simp [aggregateRaw,zeroRaw,rawWeight]
  | cons p es ih =>
      rcases p with ⟨a,b⟩
      have h := detector_sizes a b
      simp only [aggregateRaw,eraser_size,h.1,h.2,ih.1,ih.2]
      simp [rawWeight,Nat.add_assoc]

theorem magnify_size (c : Code) : (magnifyRaw c).2.1.length=c.2.1.length+3 := by
  simp [magnifyRaw,insertTable,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
theorem identity_size (c : Code) : (identityRaw c).2.1.length=c.2.1.length+3 := by
  simp [identityRaw,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
theorem constant_size (c : Code) : (constantRaw c).2.1.length=c.2.1.length+3 := by
  simp [constantRaw,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
theorem wrapper_size (upper : Bool) (c : Code) :
    (wrapperRaw upper c).2.1.length=c.2.1.length+6 := by
  cases upper <;> simp [wrapperRaw,magnify_size,identity_size,constant_size,Nat.add_assoc]

theorem rejectionAndCounts : RawDerivedCompositionTargets.RejectionAndCounts := by
  refine ⟨?_,?_,?_,detector_sizes,aggregate_sizes,wrapper_size,?_,?_,?_⟩
  · intro a b
    cases hg : eraserGuard a b <;> simp [detectors,hg]
  · intro context es
    cases hg : aggregateGuard context es <;> simp [aggregate,hg]
  · intro upper c
    cases hg : wrapperGuard c <;> simp [wrap,hg]
  · intro a b out h
    obtain ⟨Γ,aa,bb,ha,hb,ho,_⟩ := detectors_success a b out h
    rw [ho]
    exact ⟨typedAccepted _,typedAccepted _⟩
  · intro context es out h
    obtain ⟨Γ,ss,hΓ,hs,ho,_⟩ := aggregate_success context es out h
    rw [ho]
    exact ⟨typedAccepted _,typedAccepted _⟩
  · intro upper c out h
    obtain ⟨Γ,a,hc,ho,_⟩ := wrap_success upper c out h
    rw [ho]
    exact typedAccepted _
end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.DerivedComposition
