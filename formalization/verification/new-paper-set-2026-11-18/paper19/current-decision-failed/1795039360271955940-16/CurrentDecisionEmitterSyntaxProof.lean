module
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionEmitterDefinitions
public import LogicLineages.ControlSensitivityCurrent.RawBinaryPlanProof
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGOperationsStructuralProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentDecisionEmitter

open LogicLineages.OrdinalComparison.Source
open GroundEquivalence ExistentialPlan PrimitiveLowering
open RawSourceDAG (Code encode variableIndex)
open RawSourceDAG.InputCompiler (InputCode encodeInput prependStep)
open RawSourceDAG.Operations (renamingCode rename_input)
open RawSourceDAG.BinaryPlanCompiler (prefixTable prefix_table_code)
open CurrentAttainment (repeatAdd addSteps)

theorem renaming_by_index {Γ Δ} (r : Renaming Γ Δ) (n : Nat)
    (h : ∀ (τ : Ty) (y : Variable Γ τ), variableIndex (r y) = variableIndex y+n) :
    renamingCode r = prefixTable n (Γ.map SyntaxCode.typeCode) := by
  have he := RawSourceDAG.PlanCompiler.renaming_comp_codes
    (fun {τ} (x : Variable Γ τ) => x) r (fun i => i+n) (fun x => h _ x)
  rw [RawSourceDAG.PlanCompiler.identity_table] at he
  simpa only [prefixTable, List.length_map] using he

theorem lift_exact {Γ τ} (d : Input Γ τ) (n : Nat) :
    liftCode n (encode ⟨Γ,τ,d⟩) =
      encode ⟨List.replicate n Ty.ground ++ Γ,τ,ScopedDAG.renameInput (shift n) d⟩ := by
  unfold liftCode
  rw [rename_input]
  change RawSourceDAG.Operations.renameCode (List.replicate n 0 ++ Γ.map SyntaxCode.typeCode)
    (prefixTable n (Γ.map SyntaxCode.typeCode)) _ = _
  rw [prefix_table_code]
  simp [SyntaxCode.typeCode]

private theorem addSteps_succ (n k : Nat) :
    addSteps (n+1) k = ((6,1,k+1),none) :: addSteps n (k+1) := by
  unfold addSteps
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Nat.add_zero, Function.comp_def, Nat.succ_eq_add_one]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [Nat.add_right_comm]
  omega

private theorem repeat_syntax (n : Nat) {Γ : List Ty} (x a : Variable Γ .ground)
    (ha : variableIndex a = 0)
    (k : ∀ {Δ}, Renaming Γ Δ → Variable Δ .ground → InputNormalization.Input Δ 0) :
    ∃ (Δ : List Ty) (r : Renaming Γ Δ) (z : Variable Δ .ground),
      Δ.map SyntaxCode.typeCode = List.replicate n 0 ++ Γ.map SyntaxCode.typeCode ∧
      (∀ (τ : Ty) (y : Variable Γ τ), variableIndex (r y) = variableIndex y + n) ∧
      variableIndex z = 0 ∧
      encodeInput (repeatAdd x a n k) =
        (addSteps n (variableIndex x) ++ (encodeInput (k r z)).1, (encodeInput (k r z)).2) := by
  induction n generalizing Γ with
  | zero =>
    exact ⟨Γ,fun y => y,a,rfl,fun _ _ => rfl,ha,rfl⟩
  | succ n ih =>
    let k' : ∀ {Δ}, Renaming (.ground :: Γ) Δ → Variable Δ .ground → InputNormalization.Input Δ 0 :=
      fun r z => k (fun y => r (.there y)) z
    obtain ⟨Δ,r,z,ht,hr,hz,he⟩ := ih (.there x) .here rfl k'
    refine ⟨Δ,fun y => r (.there y),z,?_,?_,hz,?_⟩
    · rw [ht, List.replicate_succ', List.append_assoc]
      rfl
    · intro τ y
      rw [hr]
      simp only [RawSourceDAG.variableIndex]
      omega
    · rw [repeatAdd, encodeInput, addSteps_succ]
      change prependStep ((6,variableIndex a+1,variableIndex x+1),none)
        (encodeInput (repeatAdd (.there x) .here n k')) = _
      rw [he, ha]
      rfl

theorem observe_syntax {Γ} (a b : Input Γ .ground)
    (x y v : Variable Γ .ground) (factor anchor : Nat)
    (k : ∀ {Δ}, Renaming Γ Δ → Ports Δ → InputNormalization.Input Δ 0) :
    ∃ (Δ : List Ty) (r : Renaming Γ Δ) (z : Ports Δ),
      Δ.map SyntaxCode.typeCode = List.replicate (factor+5) 0 ++ Γ.map SyntaxCode.typeCode ∧
      (∀ (τ : Ty) (i : Variable Γ τ), variableIndex (r i) = variableIndex i + (factor+5)) ∧
      portIndices z = (factor+4,factor+3,2,0) ∧
      encodeInput (observe a b x y v factor anchor k) =
        (observeSteps (encode ⟨Γ,.ground,a⟩) (encode ⟨Γ,.ground,b⟩)
          (variableIndex x) (variableIndex y) (variableIndex v) factor anchor ++
          (encodeInput (k r z)).1, (encodeInput (k r z)).2) := by
  let Γ' := Ty.ground :: Ty.ground :: Ty.ground :: Γ
  let r0 : Renaming Γ Γ' := fun z => .there (.there (.there z))
  let cont : ∀ {Δ}, Renaming Γ' Δ → Variable Δ .ground → InputNormalization.Input Δ 0 := fun r sum =>
    .literal (factor * anchor)
      (.add (.var .here) (.var (.there (r (r0 y))))
        (k (fun z => .there (.there (r (r0 z))))
          (.there (.there (r (.there (.there .here)))),
            .there (.there (r (.there .here))), .there (.there sum), .here)))
  obtain ⟨Δ,r,sum,ht,hr,hsum,he⟩ := repeat_syntax factor (r0 v) .here rfl cont
  let Δ' := Ty.ground :: Ty.ground :: Δ
  let r' : Renaming Γ Δ' := fun z => .there (.there (r (r0 z)))
  let z : Ports Δ' := (.there (.there (r (.there (.there .here)))),
    .there (.there (r (.there .here))), .there (.there sum), .here)
  refine ⟨Δ',r',z,?_,?_,?_,?_⟩
  · change [0,0] ++ Δ.map SyntaxCode.typeCode = _
    rw [ht]
    change [0,0] ++ (List.replicate factor 0 ++ ([0,0,0] ++ Γ.map SyntaxCode.typeCode)) = _
    rw [← List.append_assoc (List.replicate factor 0) [0,0,0], ← List.append_assoc [0,0] _ _]
    change (List.replicate 2 0 ++ (List.replicate factor 0 ++ List.replicate 3 0)) ++ _ = _
    rw [List.replicate_append_replicate, List.replicate_append_replicate]
    rw [show 2+(factor+3)=factor+5 by omega]
  · intro τ i
    change variableIndex (r (r0 i)) + 1 + 1 = _
    rw [hr]
    change variableIndex i + 1 + 1 + 1 + factor + 1 + 1 = _
    omega
  · simp only [portIndices,z,RawSourceDAG.variableIndex, hr, hsum]
    congr 3 <;> omega
  · have hcode : liftCode 1 (encode ⟨Γ, .ground,b⟩) =
        encode ⟨.ground :: Γ, .ground,ScopedDAG.renameInput (Renaming.weaken Γ .ground) b⟩ :=
      lift_exact b 1
    unfold observe observeSteps
    rw [encodeInput, encodeInput, encodeInput, ← hcode]
    change prependStep ((8,0,0),some (encode ⟨Γ,.ground,a⟩))
      (prependStep ((8,0,0),some (liftCode 1 (encode ⟨Γ,.ground,b⟩)))
        (prependStep ((6,variableIndex x+3,0),none) (encodeInput (repeatAdd (r0 v) .here factor cont)))) = _
    refine (congrArg (fun c => prependStep ((8,0,0),some (encode ⟨Γ,.ground,a⟩))
      (prependStep ((8,0,0),some (liftCode 1 (encode ⟨Γ,.ground,b⟩)))
        (prependStep ((6,variableIndex x+3,0),none) c))) he).trans ?_
    have hy : variableIndex (r (r0 y)) + 1 + 1 = variableIndex y+(factor+5) := by
      rw [hr]
      change variableIndex y+1+1+1+factor+1+1 = _
      omega
    have vv : variableIndex (r0 v) = variableIndex v+3 := by
      change variableIndex v + 1 + 1 + 1 = _
      omega
    simp only [cont,encodeInput,RawSourceDAG.PrimitiveGate.encodePort,
      RawSourceDAG.variableIndex,hy,vv,prependStep,List.cons_append,List.nil_append,List.append_assoc]
    rfl

theorem rows_exact {Γ} (strict : Bool) (a b : Ports Γ) (v w : Variable Γ .ground) :
    encodeInput (finalRows strict a b v w) = rowCodes strict (portIndices a) (portIndices b)
      (variableIndex v) (variableIndex w) := by cases strict <;> rfl

end LogicLineages.ControlSensitivityCurrent.CurrentDecisionEmitter
