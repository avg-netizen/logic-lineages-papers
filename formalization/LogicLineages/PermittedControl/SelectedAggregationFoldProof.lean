module
public import LogicLineages.PermittedControl.SelectedAggregationCollisionProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedAggregation.Proof
open OrdinalComparison Source Source.AdmissibleSum SelectedSourceDomain SelectedFunctionalDetector
open SelectedFunctionalDetector.Proof
open ControlSensitivityCurrent

 theorem g_mono (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K) :
    StrictMono (PolicyCollision.g ctrl) := by
  intro a b hab
  have h := (selected_threshold_admissible ctrl K hc).1 (show a+2<b+2 by omega)
  simpa only [PolicyCollision.g] using Nat.add_lt_add_right h 1

 theorem eraser_order {Γ} (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    (policy : Policy) (ρ : AdmissibleSubstitution ctrl Γ) (a b c d : OriginalTerm Γ .ground)
    (ha : groundValue ctrl policy ρ c≤groundValue ctrl policy ρ a)
    (hb : groundValue ctrl policy ρ d≤groundValue ctrl policy ρ b) :
    groundValue ctrl policy ρ (SourceCollisionCompletion.eraser c d)≤
      groundValue ctrl policy ρ (SourceCollisionCompletion.eraser a b) ∧
    (groundValue ctrl policy ρ (SourceCollisionCompletion.eraser a b)=
      groundValue ctrl policy ρ (SourceCollisionCompletion.eraser c d) ↔
      groundValue ctrl policy ρ a=groundValue ctrl policy ρ c ∧
      groundValue ctrl policy ρ b=groundValue ctrl policy ρ d) ∧
    (¬(groundValue ctrl policy ρ a=groundValue ctrl policy ρ c ∧
      groundValue ctrl policy ρ b=groundValue ctrl policy ρ d) →
      groundValue ctrl policy ρ (SourceCollisionCompletion.eraser c d)+2≤
      groundValue ctrl policy ρ (SourceCollisionCompletion.eraser a b)) := by
  refine ⟨?_,?_,?_⟩
  · rw [eraser_control ctrl K hc policy ρ,eraser_control ctrl K hc policy ρ]
    exact (g_mono ctrl K hc).monotone (by omega)
  · rw [eraser_control ctrl K hc policy ρ,eraser_control ctrl K hc policy ρ,
      (g_mono ctrl K hc).injective.eq_iff]
    omega
  · intro hn
    have hlt : 3*groundValue ctrl policy ρ c+groundValue ctrl policy ρ d+2<
        3*groundValue ctrl policy ρ a+groundValue ctrl policy ρ b+2 := by omega
    rw [eraser_value ctrl K hc policy ρ,eraser_value ctrl K hc policy ρ]
    exact eraser_gap ctrl K hc _ _ hlt

 theorem aggregateAt {Γ} (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    (policy : Policy) (ρ : AdmissibleSubstitution ctrl Γ)
    (es : List (OriginalTerm Γ .ground × OriginalTerm Γ .ground)) :
    AggregateAt ctrl policy ρ es := by
  induction es with
  | nil =>
    refine ⟨groundResult ctrl K hc policy ρ _,groundResult ctrl K hc policy ρ _,le_rfl,?_,?_⟩
    · simp [AllEqual,SourceAggregateCompletion.aggregate]
    · simp [AllEqual,SourceAggregateCompletion.aggregate]
  | cons e es ih =>
    obtain ⟨hls,hrs,hord,heq,hgap⟩ := sixEraserCollision ctrl K hc _ policy ρ e.1 e.2
    obtain ⟨htl,htr,htord,hteq,htgap⟩ := ih
    have h := eraser_order ctrl K hc policy ρ
      (SourceCollisionCompletion.detectorLeft e.1 e.2) (SourceAggregateCompletion.aggregate es).1
      (SourceCollisionCompletion.detectorRight e.1 e.2) (SourceAggregateCompletion.aggregate es).2
      hord htord
    have hall : AllEqual ctrl policy ρ (e::es) ↔
        groundValue ctrl policy ρ e.1=groundValue ctrl policy ρ e.2 ∧ AllEqual ctrl policy ρ es := by
      simp [AllEqual,SourceAggregateCompletion.aggregate]
    refine ⟨groundResult ctrl K hc policy ρ _,groundResult ctrl K hc policy ρ _,h.1,?_,?_⟩
    · exact h.2.1.trans ((and_congr heq hteq).trans hall.symm)
    · intro hn
      apply h.2.2
      intro hh
      exact hn (hall.mpr ⟨heq.mp hh.1,hteq.mp hh.2⟩)

 theorem actualAggregation : SelectedAggregationTargets.ActualAggregation := by
  intro ctrl K hc Γ policy ρ
  exact ⟨aggregateAt ctrl K hc policy ρ,
    zero_value ctrl K hc policy ρ,zero_value ctrl K hc policy ρ⟩
end LogicLineages.PermittedControl.SelectedAggregation.Proof
