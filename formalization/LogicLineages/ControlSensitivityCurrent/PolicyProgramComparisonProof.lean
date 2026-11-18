module
public import LogicLineages.ControlSensitivityCurrent.PolicyProgramComparisonTargets
public import LogicLineages.ControlSensitivityCurrent.PolicyProgramProof
public import LogicLineages.ControlSensitivityCurrent.PolicyOrderWrapperProof
public import LogicLineages.ControlSensitivityCurrent.FullAggregateProof
public import LogicLineages.ControlSensitivityCurrent.PolicyProgramSizeProof
public import LogicLineages.OrdinalComparison.SourceGroundEquivalenceDAGProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyProgramComparison
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open GroundEquivalence ExistentialPlan

theorem holds_raw (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ} (r : Result Γ)
    (ρ : Variable r.context .ground → Nat) :
    PolicyPlan.ResultHolds p f r ρ ↔ ∀ e ∈ ScopedDAG.equations r.forest,
      PolicyCollision.rawScalar p f (inputs ρ) e.1 = PolicyCollision.rawScalar p f (inputs ρ) e.2 := by
  constructor
  · intro h e he
    obtain ⟨e',he',heq⟩ := List.mem_map.mp he
    subst e
    exact (PolicyObservation.equationCalibration p f _ _ _ _).mp (h e' he')
  · intro h e he
    apply (PolicyObservation.equationCalibration p f _ _ _ _).mpr
    exact h (e.1.term,e.2.term) (List.mem_map.mpr ⟨e,he,rfl⟩)

theorem strict_at (f : Nat → Nat) (hf : FullAddition.Targets.SourceGrowth f)
    (p : AdmissibleSum.Policy) {Γ} (q : Plan Γ)
    (ρ : Variable (compile q).context .ground → Nat) :
    PolicyCollision.rawScalar p f (inputs ρ) (strictPair q).1.term <
      PolicyCollision.rawScalar p f (inputs ρ) (strictPair q).2.term ↔
      ¬ PolicyPlan.ResultHolds p f (compile q) ρ := by
  have ht := (ScopedDAG.Proof.aggregate (compile q).context (compile q).forest).1
  have hl := congrArg Prod.fst ht
  have hr := congrArg Prod.snd ht
  dsimp only at hl hr
  change PolicyCollision.rawScalar _ _ _ (ScopedDAG.aggregate (compile q).forest).2.term <
    PolicyCollision.rawScalar _ _ _ (ScopedDAG.aggregate (compile q).forest).1.term ↔ _
  rw [hl,hr]
  have ha := FullAggregate.completeAggregate.2.2.2 f hf p (compile q).context
    (inputs ρ) (ScopedDAG.equations (compile q).forest)
  constructor
  · intro hs hh
    have he := ha.2.1.mpr ((holds_raw p f (compile q) ρ).mp hh)
    omega
  · intro hn
    have he : PolicyCollision.rawScalar p f (inputs ρ)
        (SourceAggregateCompletion.aggregate (ScopedDAG.equations (compile q).forest)).1 ≠
      PolicyCollision.rawScalar p f (inputs ρ)
        (SourceAggregateCompletion.aggregate (ScopedDAG.equations (compile q).forest)).2 := by
      intro h
      exact hn ((holds_raw p f (compile q) ρ).mpr (ha.2.1.mp h))
    have hp := ha.1
    omega

theorem wrapperSyntax : PolicyProgramComparisonTargets.WrapperSyntax := by
  intro Γ d
  exact ⟨GroundEquivalence.Proof.upper_input d,GroundEquivalence.Proof.lower_input d,
    GroundEquivalence.Proof.upper_size d,GroundEquivalence.Proof.lower_size d⟩

theorem pointwise : PolicyProgramComparisonTargets.Pointwise := by
  intro f hf p Γ q ρ
  refine ⟨strict_at f hf p q ρ,?_⟩
  change PolicyCollision.rawScalar p f (inputs ρ) (upperInput (strictPair q).1).term ≤
    PolicyCollision.rawScalar p f (inputs ρ) (lowerInput (strictPair q).2).term ↔ _
  rw [GroundEquivalence.Proof.upper_input,GroundEquivalence.Proof.lower_input]
  exact (PolicyOrderWrapper.orderConversion f hf p _ (inputs ρ) _ _).trans (strict_at f hf p q ρ)

theorem comparison : PolicyProgramComparisonTargets.Comparison := by
  intro f hf p Γ q
  have he : (∃ ρ, InputNormalization.programEval p f ρ q) ↔
      ∃ ν, PolicyPlan.ResultHolds p f (compile (BooleanCompiler.lower q)) ν := by
    constructor
    · rintro ⟨ρ,hρ⟩
      obtain ⟨ν,_,hν⟩ := ((PolicyProgram.forest f hf p Γ q).1 ρ).mp hρ
      exact ⟨ν,hν⟩
    · rintro ⟨ν,hν⟩
      refine ⟨fun x => ν ((compile (BooleanCompiler.lower q)).embedding x),?_⟩
      exact ((PolicyProgram.forest f hf p Γ q).1 _).mpr ⟨ν,fun _ => rfl,hν⟩
  constructor
  · apply Iff.trans ?_ (not_congr he).symm
    constructor
    · intro hs hh
      obtain ⟨ν,hν⟩ := hh
      exact ((pointwise f hf p Γ (BooleanCompiler.lower q) ν).1.mp (hs ν)) hν
    · intro hn ν
      exact (pointwise f hf p Γ (BooleanCompiler.lower q) ν).1.mpr (fun h => hn ⟨ν,h⟩)
  · apply Iff.trans ?_ (not_congr he).symm
    constructor
    · intro hs hh
      obtain ⟨ν,hν⟩ := hh
      exact ((pointwise f hf p Γ (BooleanCompiler.lower q) ν).2.mp (hs ν)) hν
    · intro hn ν
      exact (pointwise f hf p Γ (BooleanCompiler.lower q) ν).2.mpr (fun h => hn ⟨ν,h⟩)

theorem weight_identity {Γ} (es : List (Input Γ .ground × Input Γ .ground)) :
    ScopedDAG.weight es = 2*(es.map (fun e => e.1.specs.length+e.2.specs.length)).sum+8*es.length+1 := by
  induction es with
  | nil => simp [ScopedDAG.weight]
  | cons e es ih =>
      simp only [ScopedDAG.weight,List.map_cons,List.sum_cons,List.length_cons] at *
      omega

theorem outputSizes : PolicyProgramComparisonTargets.OutputSizes := by
  intro Γ q
  have hs := PolicyProgramSize.forestCodeCounts Γ q
  have ha := ScopedDAG.Proof.aggregate (compile (BooleanCompiler.lower q)).context
    (compile (BooleanCompiler.lower q)).forest
  have hw : ScopedDAG.weight (compile (BooleanCompiler.lower q)).forest ≤ BooleanCompiler.budget q - 6 := by
    rw [weight_identity]
    change 2*(compile (BooleanCompiler.lower q)).nodes + 8*(compile (BooleanCompiler.lower q)).forest.length+1 ≤ _
    unfold BooleanCompiler.budget
    simp only [Nat.mul_assoc] at hs ⊢
    omega
  have hb : 6 ≤ BooleanCompiler.budget q := by unfold BooleanCompiler.budget; omega
  have hl : (BooleanCompiler.strictPair q).1.specs.length ≤ BooleanCompiler.budget q - 6 := by
    change (ScopedDAG.aggregate (compile (BooleanCompiler.lower q)).forest).2.specs.length ≤ _
    rw [ha.2.2]; exact hw
  have hr : (BooleanCompiler.strictPair q).2.specs.length ≤ BooleanCompiler.budget q - 6 := by
    change (ScopedDAG.aggregate (compile (BooleanCompiler.lower q)).forest).1.specs.length ≤ _
    rw [ha.2.1]; exact hw
  refine ⟨by omega,by omega,?_,?_⟩
  · change (upperInput (BooleanCompiler.strictPair q).1).specs.length ≤ _
    rw [GroundEquivalence.Proof.upper_size]; omega
  · change (lowerInput (BooleanCompiler.strictPair q).2).specs.length ≤ _
    rw [GroundEquivalence.Proof.lower_size]; omega
end LogicLineages.ControlSensitivityCurrent.PolicyProgramComparison
