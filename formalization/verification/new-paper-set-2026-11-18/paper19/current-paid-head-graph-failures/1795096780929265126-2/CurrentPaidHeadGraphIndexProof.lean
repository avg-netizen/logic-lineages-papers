module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphFoundationTargets
public import LogicLineages.ControlSensitivityCurrent.CurrentUnitEliminationProjectionProof
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGValidationProof
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGOperationsReferenceProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
open LogicLineages.OrdinalComparison.Source
open RawSourceDAG (variableIndex getVariable)
open CurrentUnitElimination (WireCtx groundCtx shift)

theorem indexBound {Γ σ} (x : Variable Γ σ) : variableIndex x < Γ.length := by
  induction x with
  | here => simp [variableIndex]
  | there x ih => simpa only [variableIndex,List.length_cons,Nat.add_lt_add_iff_right] using ih

theorem indexInj {Γ σ} : Function.Injective (variableIndex (Γ:=Γ) (τ:=σ)) := by
  intro x y h
  have a := RawSourceDAG.variable_roundtrip x
  have b := RawSourceDAG.variable_roundtrip y
  rw [h] at a
  exact Option.some.inj (a.symm.trans b)

theorem atIndex : ∀ {Γ : List Ty} (i : Nat), i < Γ.length →
    ∃ (σ : Ty) (x : Variable Γ σ), variableIndex x = i
  | [],i,h => by simp at h
  | σ::Γ,0,_ => ⟨σ,.here,rfl⟩
  | σ::Γ,i+1,h => by
    obtain ⟨τ,x,e⟩ := atIndex (Γ:=Γ) i (by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using h)
    exact ⟨τ,.there x,congrArg (·+1) e⟩

theorem indexType {Γ σ} (x : Variable Γ σ) :
    (Γ.map SyntaxCode.typeCode).getD (variableIndex x) 1 = SyntaxCode.typeCode σ := by
  induction x with
  | here => rfl
  | there x ih => simpa only [List.map_cons,variableIndex,List.getD_cons_succ] using ih

theorem shiftedIndex {Γ σ} (n : Nat) (x : Variable Γ σ) :
    variableIndex (shift n x) = n+variableIndex x := by
  induction n with
  | zero => simp only [shift,Nat.zero_add]
  | succ n ih => simp only [shift,variableIndex,ih]; omega

theorem widthLength (n : Nat) (Γ : List Ty) : (WireCtx n Γ).length = n+Γ.length := by
  induction n with
  | zero => simp [WireCtx]
  | succ n ih => simp only [WireCtx,List.length_cons,ih]; omega

theorem mappedWidth (n : Nat) (Γ : List Ty) :
    (WireCtx n Γ).map SyntaxCode.typeCode = List.replicate n 0 ++ Γ.map SyntaxCode.typeCode := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [WireCtx,List.map_cons,List.replicate_succ,List.cons_append,ih]; rfl

theorem allGroundMap (Γ : List Ty) (hg : ∀ σ ∈ Γ, σ = .ground) :
    Γ.map SyntaxCode.typeCode = List.replicate Γ.length 0 := by
  induction Γ with
  | nil => rfl
  | cons σ Γ ih =>
    have hσ : σ = .ground := hg σ (by simp)
    obtain rfl := hσ
    rw [List.map_cons,List.length_cons,List.replicate_succ,ih (fun τ ht => hg τ (by simp [ht]))]
    rfl

theorem countGround (Γ : List Ty) : groundCount (Γ.map SyntaxCode.typeCode) = (groundCtx Γ).length := by
  induction Γ with
  | nil => rfl
  | cons σ Γ ih =>
    cases σ with
    | ground => simpa [groundCount,SyntaxCode.typeCode,groundCtx] using ih
    | arrow a b => simpa [groundCount,SyntaxCode.typeCode,SyntaxCode.arrowCode,groundCtx] using ih

theorem groundRankIndex {Γ} (x : Variable Γ .ground) :
    (groundRank x).val = variableIndex (CurrentUnitElimination.selectGround x) := by
  induction Γ with
  | nil => exact nomatch x
  | cons σ Γ ih =>
    cases σ with
    | ground =>
      cases x with
      | here => rfl
      | there x => exact congrArg (·+1) (ih x)
    | arrow a b =>
      cases x with
      | there x => exact ih x

theorem groundRankCount {Γ} (x : Variable Γ .ground) :
    (groundRank x).val = groundCount ((Γ.map SyntaxCode.typeCode).take (variableIndex x)) := by
  induction Γ with
  | nil => exact nomatch x
  | cons σ Γ ih =>
    cases σ with
    | ground =>
      cases x with
      | here => rfl
      | there x =>
        change (groundRank x).val+1=groundCount ((0 :: Γ.map SyntaxCode.typeCode).take (variableIndex x+1))
        simpa [groundCount] using ih x
    | arrow a b =>
      cases x with
      | there x =>
        change (groundRank x).val=groundCount ((SyntaxCode.arrowCode (SyntaxCode.typeCode a)
          (SyntaxCode.typeCode b)::Γ.map SyntaxCode.typeCode).take (variableIndex x+1))
        simpa [groundCount, SyntaxCode.arrowCode] using ih x

theorem newGroundIndex (Γ : List Ty) {n : Nat} (i : Fin n) :
    variableIndex (newGround Γ i) = i.val := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change variableIndex (newGround Γ j)+1 = j.val+1
      rw [ih]

theorem freshGroundIndex {Γ} (x : Variable Γ .ground) :
    variableIndex (freshRename Γ x) = (groundRank x).val := newGroundIndex Γ (groundRank x)

theorem freshContextExact (Γ : List Ty) :
    freshContext (Γ.map SyntaxCode.typeCode) = (FreshCtx Γ).map SyntaxCode.typeCode := by
  rw [freshContext,countGround,mappedWidth]

theorem tableByIndex {Γ Δ} (r : Renaming Γ Δ) (mapIndex : Nat → Nat)
    (h : ∀ {σ} (x : Variable Γ σ), mapIndex (variableIndex x)=variableIndex (r x)) :
    (List.range Γ.length).map mapIndex = RawSourceDAG.Operations.renamingCode r := by
  apply List.ext_getElem
  · simp [RawSourceDAG.Operations.renaming_length]
  · intro i ha hb
    have hi : i<Γ.length := by simpa using ha
    obtain ⟨σ,x,hx⟩ := atIndex i hi
    have hr := RawSourceDAG.Operations.renaming_lookup r x
    rw [hx,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hb,Option.getD_some] at hr
    rw [List.getElem_map,List.getElem_range]
    exact (hx ▸ h x).trans hr.symm

theorem freshTableExact (Γ : List Ty) :
    freshTable (Γ.map SyntaxCode.typeCode)=RawSourceDAG.Operations.renamingCode (freshRename Γ) := by
  unfold freshTable
  rw [List.length_map]
  apply tableByIndex
  intro σ x
  rw [indexType x]
  cases σ with
  | ground => simp only [SyntaxCode.typeCode,↓reduceIte,freshGroundIndex,groundRankCount]
  | arrow a b =>
    simp only [SyntaxCode.typeCode,SyntaxCode.arrowCode,Nat.add_one_ne_zero,if_false,countGround]
    exact (shiftedIndex _ x).symm

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
