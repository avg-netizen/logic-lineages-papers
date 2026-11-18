module
public import LogicLineages.ControlSensitivityCurrent.CurrentAttainmentTargets
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentAttainment

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open ExistentialPlan PrimitiveLowering
open RawSourceDAG (variableIndex)
open RawSourceDAG.InputCompiler (encodeInput)

private theorem addSteps_succ (n k : Nat) :
    addSteps (n+1) k = ((6,1,k+1),none) :: addSteps n (k+1) := by
  unfold addSteps
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Nat.add_zero, Function.comp_def, Nat.succ_eq_add_one]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [Nat.add_right_comm]

private theorem repeat_syntax (n : Nat) {Γ : List Ty} (x a : Variable Γ .ground)
    (ha : variableIndex a = 0)
    (k : ∀ {Δ}, Renaming Γ Δ → Variable Δ .ground → InputNormalization.Input Δ 0) :
    ∃ (Δ : List Ty) (r : Renaming Γ Δ) (z : Variable Δ .ground),
      (∀ (τ : Ty) (y : Variable Γ τ), variableIndex (r y) = variableIndex y + n) ∧
      variableIndex z = 0 ∧
      encodeInput (repeatAdd x a n k) =
        (addSteps n (variableIndex x) ++ (encodeInput (k r z)).1, (encodeInput (k r z)).2) := by
  induction n generalizing Γ with
  | zero =>
    exact ⟨Γ,fun y => y,a,fun _ _ => rfl,ha,rfl⟩
  | succ n ih =>
    let k' : ∀ {Δ}, Renaming (.ground :: Γ) Δ → Variable Δ .ground → InputNormalization.Input Δ 0 :=
      fun r z => k (fun y => r (.there y)) z
    obtain ⟨Δ,r,z,hr,hz,he⟩ := ih (.there x) .here rfl k'
    refine ⟨Δ,fun y => r (.there y),z,?_,hz,?_⟩
    · intro τ y
      rw [hr]
      simp [RawSourceDAG.variableIndex, Nat.add_right_comm]
    · rw [repeatAdd, encodeInput, addSteps_succ]
      change RawSourceDAG.InputCompiler.prependStep
        ((6,variableIndex a+1,variableIndex x+1),none)
        (encodeInput (repeatAdd (.there x) .here n k')) = _
      rw [he, ha]
      rfl

theorem tailSyntax : CurrentAttainmentTargets.TailSyntax := by
  intro h c q
  unfold tailProgram tailCode
  rw [encodeInput]
  let left : ∀ {Δ}, Renaming (.ground :: List.replicate 2 Ty.ground) Δ →
      Variable Δ .ground → InputNormalization.Input Δ 0 :=
    fun r a =>
      .unary h a (.literal (residue q)
        (repeatAdd (.there (.there (r (.there (.there .here))))) .here q.2.2.1
          (fun s b => .boolean (.eq (.var (s (.there .here))) (.var b)) (.finish 0))))
  obtain ⟨Δ,r,a,hr,ha,eh⟩ := repeat_syntax q.1 (.there .here : Variable
    (.ground :: List.replicate 2 Ty.ground) .ground) .here rfl left
  change RawSourceDAG.InputCompiler.prependStep ((7,bound c q-c,0),none)
    (encodeInput (repeatAdd (.there .here) .here q.1 left)) = _
  rw [eh]
  let right : ∀ {Ξ}, Renaming (.ground :: .ground :: Δ) Ξ →
      Variable Ξ .ground → InputNormalization.Input Ξ 0 :=
    fun s b => .boolean (.eq (.var (s (.there .here))) (.var b)) (.finish 0)
  let y : Variable (.ground :: .ground :: Δ) .ground := .there (.there (r (.there (.there .here))))
  obtain ⟨Ξ,s,b,hs,hb,es⟩ := repeat_syntax q.2.2.1 y .here rfl right
  have hy : variableIndex y = q.1+4 := by
    dsimp only [y,RawSourceDAG.variableIndex]
    rw [hr]
    simp only [RawSourceDAG.variableIndex]
    omega
  have hu : variableIndex (s (.there .here : Variable (.ground :: .ground :: Δ) .ground)) + 1 =
      q.2.2.1+2 := by
    rw [hs]
    simp only [RawSourceDAG.variableIndex]
    omega
  simp only [left, encodeInput]
  change RawSourceDAG.InputCompiler.prependStep ((7,bound c q-c,0),none)
    (addSteps q.1 1 ++ (RawSourceDAG.InputCompiler.prependStep ((9,variableIndex a,0),some _)
      (RawSourceDAG.InputCompiler.prependStep ((7,residue q,0),none)
        (encodeInput (repeatAdd y .here q.2.2.1 right)))).1,
      (RawSourceDAG.InputCompiler.prependStep ((9,variableIndex a,0),some _)
      (RawSourceDAG.InputCompiler.prependStep ((7,residue q,0),none)
        (encodeInput (repeatAdd y .here q.2.2.1 right)))).2) = _
  rw [es, hy, ha]
  simp only [right, encodeInput, RawSourceDAG.InputCompiler.encodeInputRow,
    RawSourceDAG.PrimitiveGate.encodePort, hu, hb, Nat.zero_add,
    RawSourceDAG.InputCompiler.prependStep, Fin.val_zero]
  simp only [List.cons_append, List.nil_append, List.append_assoc]

end LogicLineages.ControlSensitivityCurrent.CurrentAttainment
