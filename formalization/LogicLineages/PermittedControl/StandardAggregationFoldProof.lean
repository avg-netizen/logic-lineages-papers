module
public import LogicLineages.PermittedControl.StandardAggregationCollisionProof
@[expose] public section
namespace LogicLineages.PermittedControl.StandardAggregation.Proof
open OrdinalComparison Source Source.AdmissibleSum SelectedSourceDomain SelectedFunctionalDetector
open StandardFunctionalDetector.Proof
open SelectedAggregation
open ControlSensitivityCurrent

 theorem g_mono  :
    StrictMono (PolicyCollision.g Phi) := by
  intro a b hab
  have h := Phi_strictMono (show a+2<b+2 by omega)
  simpa only [PolicyCollision.g] using Nat.add_lt_add_right h 1

 theorem eraser_order {Γ} 
    (policy : Policy) (ρ : AdmissibleSubstitution Phi Γ) (a b c d : OriginalTerm Γ .ground)
    (ha : groundValue Phi policy ρ c≤groundValue Phi policy ρ a)
    (hb : groundValue Phi policy ρ d≤groundValue Phi policy ρ b) :
    groundValue Phi policy ρ (SourceCollisionCompletion.eraser c d)≤
      groundValue Phi policy ρ (SourceCollisionCompletion.eraser a b) ∧
    (groundValue Phi policy ρ (SourceCollisionCompletion.eraser a b)=
      groundValue Phi policy ρ (SourceCollisionCompletion.eraser c d) ↔
      groundValue Phi policy ρ a=groundValue Phi policy ρ c ∧
      groundValue Phi policy ρ b=groundValue Phi policy ρ d) ∧
    (¬(groundValue Phi policy ρ a=groundValue Phi policy ρ c ∧
      groundValue Phi policy ρ b=groundValue Phi policy ρ d) →
      groundValue Phi policy ρ (SourceCollisionCompletion.eraser c d)+2≤
      groundValue Phi policy ρ (SourceCollisionCompletion.eraser a b)) := by
  refine ⟨?_,?_,?_⟩
  · rw [eraser_control  policy ρ,eraser_control  policy ρ]
    exact (g_mono ).monotone (by omega)
  · rw [eraser_control  policy ρ,eraser_control  policy ρ,
      (g_mono ).injective.eq_iff]
    omega
  · intro hn
    have hlt : 3*groundValue Phi policy ρ c+groundValue Phi policy ρ d+2<
        3*groundValue Phi policy ρ a+groundValue Phi policy ρ b+2 := by omega
    rw [eraser_value  policy ρ,eraser_value  policy ρ]
    exact eraser_gap  _ _ hlt

 theorem aggregateAt {Γ} 
    (policy : Policy) (ρ : AdmissibleSubstitution Phi Γ)
    (es : List (OriginalTerm Γ .ground × OriginalTerm Γ .ground)) :
    AggregateAt Phi policy ρ es := by
  induction es with
  | nil =>
    refine ⟨groundResult  policy ρ _,groundResult  policy ρ _,le_rfl,?_,?_⟩
    · simp [AllEqual,SourceAggregateCompletion.aggregate]
    · simp [AllEqual,SourceAggregateCompletion.aggregate]
  | cons e es ih =>
    obtain ⟨hls,hrs,hord,heq,hgap⟩ := sixEraserCollision  _ policy ρ e.1 e.2
    obtain ⟨htl,htr,htord,hteq,htgap⟩ := ih
    have h := eraser_order  policy ρ
      (SourceCollisionCompletion.detectorLeft e.1 e.2) (SourceAggregateCompletion.aggregate es).1
      (SourceCollisionCompletion.detectorRight e.1 e.2) (SourceAggregateCompletion.aggregate es).2
      hord htord
    have hall : AllEqual Phi policy ρ (e::es) ↔
        groundValue Phi policy ρ e.1=groundValue Phi policy ρ e.2 ∧ AllEqual Phi policy ρ es := by
      simp [AllEqual,SourceAggregateCompletion.aggregate]
    refine ⟨groundResult  policy ρ _,groundResult  policy ρ _,h.1,?_,?_⟩
    · exact h.2.1.trans ((and_congr heq hteq).trans hall.symm)
    · intro hn
      apply h.2.2
      intro hh
      exact hn (hall.mpr ⟨heq.mp hh.1,hteq.mp hh.2⟩)

 theorem actualAggregation : StandardAggregation.ActualAggregation := by
  intro Γ policy ρ
  exact ⟨aggregateAt  policy ρ,
    zero_value  policy ρ,zero_value  policy ρ⟩
end LogicLineages.PermittedControl.StandardAggregation.Proof
