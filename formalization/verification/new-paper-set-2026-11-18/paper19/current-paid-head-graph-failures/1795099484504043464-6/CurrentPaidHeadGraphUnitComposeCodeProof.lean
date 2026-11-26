module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphUnitLayoutCodeProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.UnitCode
open LogicLineages.OrdinalComparison.Source
open CurrentUnitElimination CurrentOneUnit
open RawSourceDAG (variableIndex)

private theorem varGround {Γ} (hg : ∀ τ ∈ Γ, τ = .ground) :
    ∀ {τ} (_ : Variable Γ τ), τ = .ground := by
  intro τ x
  have mem {Δ : List Ty} {σ : Ty} (v : Variable Δ σ) : σ ∈ Δ := by
    induction v with
    | here => simp
    | there _ ih => exact List.mem_cons_of_mem _ ih
  exact hg τ (mem x)

private theorem headGround {Γ : List Ty} (hg : ∀ τ ∈ Γ, τ = .ground) :
    ∀ τ ∈ .ground :: Γ, τ = .ground := by
  intro τ h
  rcases List.mem_cons.mp h with rfl|h
  · rfl
  · exact hg τ h

private theorem castFrame (base : List Ty) (m n : Nat)
    (a : SourceAST.Formula (.ground::.ground::WireCtx m (WireCtx n base))) :
    MatrixCode.formula (renameFormula (fun {τ} x => cast
      (congrArg (fun Δ => Variable (.ground::.ground::Δ) τ) (wireCtx_add m n base).symm) x) a) =
    MatrixCode.formula a := by
  let h := congrArg (fun Δ => Ty.ground::Ty.ground::Δ) (wireCtx_add m n base).symm
  exact formulaCast h a

private theorem freeTable {Γ : List Ty} (w : Nat) :
    let Δ := .ground :: WireCtx w (.ground :: Γ)
    let r₀ : Renaming (WireCtx w Γ) Δ := fun x => .there (under (Renaming.weaken Γ .ground) w x)
    (List.range (w+1+Γ.length)).map (fun i => if i=w then 0 else i+1) =
      RawSourceDAG.Operations.renamingCode (reroute w r₀ .here) := by
  dsimp only
  have hlen : (WireCtx w (.ground::Γ)).length = w+1+Γ.length := by
    rw [widthLength,List.length_cons]; omega
  rw [← hlen]
  apply tableByIndex
  intro τ x
  symm
  rw [rerouteIndex w _ .here (fun i => if i<w then i+1 else i+2)]
  · simp only [variableIndex]
    split
    · rfl
    · rename_i he
      by_cases hu : variableIndex x < w
      · simp [hu]
      · have h₁ : 0 < variableIndex x := by omega
        have h₂ : ¬ variableIndex x-1 < w := by omega
        simp only [hu,h₂,if_false]
        omega
  · intro υ u
    change variableIndex (under (Renaming.weaken Γ .ground) w u)+1 = _
    rw [underIndex w _ (fun i => i+1) (fun _ => rfl)]
    split <;> omega

theorem freeBlockExact {Γ : List Ty} (hg : ∀ τ ∈ Γ, τ = .ground)
    (row : LinearCode) (q : OpenGraph Γ) :
    freeBlock Γ.length row (typedBlock q) = typedBlock (freeGraph row q) := by
  let w := q.width
  let Δ := .ground :: WireCtx w (.ground :: Γ)
  let r₀ : Renaming (WireCtx w Γ) Δ := fun x => .there (under (Renaming.weaken Γ .ground) w x)
  let r : Renaming (WireCtx w (.ground::Γ)) Δ := reroute w r₀ .here
  have hctx : Δ.map SyntaxCode.typeCode = bitCtx (w+1+1+Γ.length) := by
    have hΔ : ∀ τ ∈ Δ, τ = .ground := headGround (groundWireCtx w _ (headGround hg))
    rw [allGroundMap Δ hΔ]
    unfold bitCtx
    congr 1
    simp only [Δ,List.length_cons,widthLength]
    omega
  have hform := MatrixCode.formulaRename r q.matrix
  rw [hctx,← freeTable (Γ:=Γ) w] at hform
  change (w+1,MatrixCode.both _ _) =
    (w+1,MatrixCode.formula (.conj (renameFormula r q.matrix)
      (rowFormula row (raw (.here : Variable Δ .ground)) (.literal 0) (raw (.there (shift w .here))))))
  simp only [hform,MatrixCode.formula,rowsExact,raw,MatrixCode.term,MatrixCode.raw,
    variableIndex,shiftedIndex,Nat.add_zero]

private theorem activeTable {Γ : List Ty} (b c : Nat) :
    let Δ := .ground::.ground::WireCtx b (WireCtx c (.ground::Γ))
    let l : Renaming (WireCtx b Γ) Δ := fun x => .there (.there
      (under (fun x => shift c (.there x)) b x))
    let r : Renaming (WireCtx c Γ) Δ := fun x => .there (.there
      (shift b (under (Renaming.weaken Γ .ground) c x)))
    (List.range (b+1+Γ.length)).map (fun i => if i<b then i+2 else if i=b then 0 else i+c+2) =
      RawSourceDAG.Operations.renamingCode (reroute b l .here) ∧
    (List.range (c+1+Γ.length)).map (fun i => if i=c then 1 else i+b+2) =
      RawSourceDAG.Operations.renamingCode (reroute c r (.there .here)) := by
  dsimp only
  let Δ := .ground::.ground::WireCtx b (WireCtx c (.ground::Γ))
  let l : Renaming (WireCtx b Γ) Δ := fun x => .there (.there (under (fun x => shift c (.there x)) b x))
  let r : Renaming (WireCtx c Γ) Δ := fun x => .there (.there
    (shift b (under (Renaming.weaken Γ .ground) c x)))
  have hL (τ : Ty) (x : Variable (WireCtx b Γ) τ) :
      variableIndex (l x)=if variableIndex x<b then variableIndex x+2 else variableIndex x+c+3 := by
    simp only [l,variableIndex]
    rw [underIndex b _ (fun i => c+(i+1)) (fun z => shiftedIndex c (.there z))]
    split <;> omega
  have hR (τ : Ty) (x : Variable (WireCtx c Γ) τ) :
      variableIndex (r x)=if variableIndex x<c then variableIndex x+b+2 else variableIndex x+b+3 := by
    simp only [r,variableIndex,shiftedIndex]
    rw [underIndex c _ (fun i => i+1) (fun _ => rfl)]
    split <;> omega
  have len (w : Nat) : (WireCtx w (.ground::Γ)).length=w+1+Γ.length := by
    rw [widthLength,List.length_cons]; omega
  constructor
  · rw [← len b]
    apply tableByIndex
    intro τ x
    symm
    rw [rerouteIndex b l .here (fun i => if i<b then i+2 else i+c+3) (fun x => hL _ x)]
    by_cases h : variableIndex x<b
    · have he : variableIndex x ≠ b := by omega
      simp only [h,he,if_true,if_false]
    · by_cases he : variableIndex x=b
      · simp only [h,he,if_true,if_false,variableIndex]
      · have hp : ¬ variableIndex x-1<b := by omega
        simp only [h,he,hp,if_false]
        omega
  · rw [← len c]
    apply tableByIndex
    intro τ x
    symm
    rw [rerouteIndex c r (.there .here) (fun i => if i<c then i+b+2 else i+b+3) (fun x => hR _ x)]
    by_cases he : variableIndex x=c
    · simp only [he,if_true,variableIndex,Nat.zero_add]
    · by_cases h : variableIndex x<c
      · simp only [he,h,if_true,if_false]
      · have hp : ¬ variableIndex x-1<c := by omega
        simp only [he,h,hp,if_false]
        omega

theorem activeBlockExact {Γ : List Ty} (hg : ∀ τ ∈ Γ, τ = .ground)
    (row : LinearCode) (q s : OpenGraph Γ) :
    activeBlock Γ.length row (typedBlock q) (typedBlock s) = typedBlock (activeGraph row q s) := by
  let b := q.width
  let c := s.width
  let Δ := .ground::.ground::WireCtx b (WireCtx c (.ground::Γ))
  let l : Renaming (WireCtx b Γ) Δ := fun x => .there (.there (under (fun x => shift c (.there x)) b x))
  let r : Renaming (WireCtx c Γ) Δ := fun x => .there (.there
    (shift b (under (Renaming.weaken Γ .ground) c x)))
  have hctx : Δ.map SyntaxCode.typeCode = bitCtx (b+c+2+1+Γ.length) := by
    have hΔ : ∀ τ ∈ Δ, τ = .ground :=
      headGround (headGround (groundWireCtx b _ (groundWireCtx c _ (headGround hg))))
    rw [allGroundMap Δ hΔ]
    unfold bitCtx
    congr 1
    simp only [Δ,List.length_cons,widthLength]
    omega
  have hl := MatrixCode.formulaRename (reroute b l .here) q.matrix
  have hr := MatrixCode.formulaRename (reroute c r (.there .here)) s.matrix
  have ht := activeTable (Γ:=Γ) b c
  rw [hctx,← ht.1] at hl
  rw [hctx,← ht.2] at hr
  let M : SourceAST.Formula Δ := .conj
    (.conj (renameFormula (reroute b l .here) q.matrix)
      (renameFormula (reroute c r (.there .here)) s.matrix))
    (rowFormula row (raw .here) (raw (.there .here))
      (raw (.there (.there (shift b (shift c .here))))))
  have hCast : MatrixCode.formula (activeGraph row q s).matrix = MatrixCode.formula M :=
    castFrame (.ground::Γ) b c M
  have hWidth : (activeGraph row q s).width = b+c+2 := rfl
  simp only [activeBlock,typedBlock,hWidth,hCast,M,MatrixCode.formula,rowsExact,raw,
    MatrixCode.raw,MatrixCode.term,variableIndex,shiftedIndex,Nat.add_zero,hl,hr,b,c,l,r,Δ] <;> rfl

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.UnitCode
