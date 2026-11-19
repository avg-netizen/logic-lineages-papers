module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphMatrixRowsProof
public import LogicLineages.ControlSensitivityCurrent.CurrentProbeCodeProof
public import LogicLineages.ControlSensitivityCurrent.CurrentUnitEliminationWireProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.UnitCode
open LogicLineages.OrdinalComparison.Source
open GroundEquivalence CurrentUnitElimination CurrentOneUnit
open RawSourceDAG (encode variableIndex)

/-- Payload is independent of proof-erased context transports. -/
def typedBlock {Γ} (q : OpenGraph Γ) : Block := (q.width,MatrixCode.formula q.matrix)

theorem blockCast {Γ Δ} (h : Γ=Δ) (q : OpenGraph Γ) :
    typedBlock (h ▸ q : OpenGraph Δ) = typedBlock q := by cases h; rfl

theorem indexCast {Γ Δ σ} (h : Γ=Δ) (x : Variable Γ σ) :
    variableIndex (cast (congrArg (fun C => Variable C σ) h) x)=variableIndex x := by cases h; rfl

private theorem prefixIdentity {Γ σ} (ps : List Ty) (x : Variable (ps++Γ) σ) :
    ScopedDAG.prefixRename (fun y => y) ps x = x := by
  induction ps with
  | nil => rfl
  | cons τ ps ih =>
    cases x with
    | here => rfl
    | there x => exact congrArg Variable.there (ih x)

private theorem dagIdentity {Γ ss} (d : DAG Γ ss) : ScopedDAG.rename (fun x => x) d=d := by
  induction d <;> simp only [ScopedDAG.rename,prefixIdentity,*]

private theorem inputIdentity {Γ τ} (a : Input Γ τ) : ScopedDAG.renameInput (fun x => x) a=a := by
  cases a with
  | mk ss g r => simp only [ScopedDAG.renameInput,dagIdentity]

private theorem termId {Γ} (a : SourceAST.Term Γ) : renameTerm (fun x => x) a=a := by
  induction a <;> simp only [renameTerm,inputIdentity,*]

private theorem formulaId {Γ} (a : SourceAST.Formula Γ) : renameFormula (fun x => x) a=a := by
  induction a <;> simp only [renameFormula,termId,*]

theorem formulaCast {Γ Δ} (h : Γ=Δ) (a : SourceAST.Formula Γ) :
    MatrixCode.formula (renameFormula (fun {σ} x => cast (congrArg (fun C => Variable C σ) h) x) a) =
      MatrixCode.formula a := by
  cases h
  rw [show (fun {σ} (x : Variable Γ σ) => cast (congrArg (fun C => Variable C σ) rfl) x) =
    (fun {σ} (x : Variable Γ σ) => x) from rfl,formulaId]

theorem timesExact {Γ} (n : Nat) (a : SourceAST.Term Γ) :
    MatrixCode.term (times n a)=MatrixCode.times n (MatrixCode.term a) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [times,MatrixCode.term,MatrixCode.times,Nat.rec_succ,←MatrixCode.times,ih]

theorem rowsExact {Γ} (row : LinearCode) (a b c : SourceAST.Term Γ) :
    MatrixCode.formula (rowFormula row a b c)=rawRow row (MatrixCode.term a) (MatrixCode.term b) (MatrixCode.term c) := by
  simp only [rowFormula,MatrixCode.formula,MatrixCode.term,timesExact,rawRow]

theorem underIndex {Γ Δ σ} (n : Nat) (r : Renaming Γ Δ) (k : Nat → Nat)
    (hr : ∀ {τ} (x : Variable Γ τ), variableIndex (r x)=k (variableIndex x))
    (x : Variable (WireCtx n Γ) σ) :
    variableIndex (under r n x) = if variableIndex x<n then variableIndex x else n+k (variableIndex x-n) := by
  induction n with
  | zero => simpa only [under, Nat.not_lt_zero,if_false,Nat.zero_add,Nat.sub_zero] using hr x
  | succ n ih =>
    cases x with
    | here => simp [under,Renaming.lift,variableIndex]
    | there x =>
      change variableIndex (under r n x)+1 =
        if variableIndex x+1<n+1 then variableIndex x+1 else (n+1)+k (variableIndex x+1-(n+1))
      rw [ih]
      simp only [Nat.add_lt_add_iff_right,Nat.add_sub_add_right]
      split <;> omega

theorem rerouteIndex {Γ Δ σ} (n : Nat) (r : Renaming (WireCtx n Γ) Δ) (z : Variable Δ .ground)
    (k : Nat → Nat) (hr : ∀ {τ} (x : Variable (WireCtx n Γ) τ), variableIndex (r x)=k (variableIndex x))
    (x : Variable (WireCtx n (.ground::Γ)) σ) :
    variableIndex (reroute n r z x) = if variableIndex x=n then variableIndex z
      else k (if variableIndex x<n then variableIndex x else variableIndex x-1) := by
  induction n generalizing Δ with
  | zero =>
    cases x with
    | here => rfl
    | there x =>
      simpa only [reroute,variableIndex,Nat.add_one_ne_zero,if_false,Nat.not_lt_zero,Nat.add_sub_cancel] using hr x
  | succ n ih =>
    cases x with
    | here =>
      change variableIndex (r .here) = if 0=n+1 then _ else k (if 0<n+1 then 0 else 0-1)
      simpa only [Nat.zero_ne_add_one,Nat.zero_lt_succ,if_false,if_true,variableIndex] using hr .here
    | there x =>
      have ht (τ : Ty) (u : Variable (WireCtx n Γ) τ) :
          variableIndex (r (.there u))=k (variableIndex u+1) := hr (.there u)
      change variableIndex (reroute n (fun u => r (.there u)) z x) = _
      rw [ih (fun u => r (.there u)) z (fun j => k (j+1)) (fun x => ht _ x) x]
      simp only [variableIndex,Nat.add_left_cancel_iff,Nat.add_lt_add_iff_right,Nat.add_sub_cancel]
      split
      · rfl
      · rename_i h
        by_cases hi : variableIndex x<n
        · simp only [hi,if_true]
        · have hp : 0<variableIndex x := by omega
          simp only [hi,if_false,Nat.sub_add_cancel (Nat.succ_le_of_lt hp)]

private def eraserLift (Γ : List Ty) : Renaming (.ground::.ground::Γ) (.ground::.ground::.ground::Γ) :=
  Renaming.lift (Renaming.lift (Renaming.weaken Γ .ground))

private theorem shiftedEraser {Γ} (d : Input (.ground::.ground::Γ) .ground) :
    shiftEraser (encode ⟨.ground::.ground::Γ,.ground,d⟩) =
      encode ⟨.ground::.ground::.ground::Γ,.ground,ScopedDAG.renameInput (eraserLift Γ) d⟩ := by
  rw [RawSourceDAG.Operations.rename_input]
  have ht : RawSourceDAG.Operations.renamingCode (eraserLift Γ) =
      0::1::((List.range Γ.length).map (fun i => i+3)) := by
    rw [RawSourceDAG.Operations.renamingCode,RawSourceDAG.Operations.renamingCode]
    change 0::1::RawSourceDAG.Operations.renamingCode (fun {σ} (x : Variable Γ σ) => .there (.there (.there x))) = _
    rw [← tableByIndex _ (fun i => i+3) (fun x => by simp [variableIndex]; omega)]
  simp [shiftEraser,RawSourceDAG.encode,List.map_cons,SyntaxCode.typeCode,ht]

theorem groundBlockExact (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ τ}
    (hg : ∀ σ ∈ Γ, σ = .ground) (a : Input Γ τ) :
    groundBlock p f (encode ⟨Γ,τ,a⟩)=typedBlock (groundGraph p f hg a) := by
  let da := encode ⟨Γ,τ,a⟩
  let Δ := Ty.ground::Ty.ground::Γ
  let d₀ := ScopedDAG.renameInput (AbsoluteObserver.shiftTwo Γ) a
  let d₁ := ScopedDAG.renameInput (AbsoluteObserver.fromEmpty Δ) (AbsoluteProbeDAG.closeInput hg a)
  have h0 : CurrentDecisionEmitter.liftCode 2 da = encode ⟨Δ,τ,d₀⟩ := by
    apply MatrixCode.actualLift
    exact MatrixCode.prefixComp (MatrixCode.prefixOne Γ) (MatrixCode.prefixOne (.ground::Γ))
  have h1 : RawSourceDAG.Operations.renameCode (0::0::da.1) [] (CurrentProbeCode.closeRaw da) =
      encode ⟨Δ,τ,d₁⟩ := by
    rw [CurrentProbeCode.exactClosing Γ τ hg a,RawSourceDAG.Operations.rename_input]
    rfl
  have h2 := CurrentProbeCode.exactProbe Δ τ d₀ .here
  have h3 := CurrentProbeCode.exactProbe Δ τ d₁ (.there .here)
  have hl : originalEraser da = encode ⟨.ground::.ground::.ground::Γ,.ground,
      ScopedDAG.renameInput (eraserLift Γ) (AbsoluteProbeDAG.originalInput a)⟩ := by
    unfold originalEraser
    rw [h0]
    change CurrentProbeCode.probeRaw (encode ⟨Δ,τ,d₀⟩) 0 = _ at h2
    rw [h2]
    exact shiftedEraser _
  have hr : closedEraser da = encode ⟨.ground::.ground::.ground::Γ,.ground,
      ScopedDAG.renameInput (eraserLift Γ) (AbsoluteProbeDAG.closedInput hg a)⟩ := by
    unfold closedEraser
    rw [h1]
    change CurrentProbeCode.probeRaw (encode ⟨Δ,τ,d₁⟩) 1 = _ at h3
    rw [h3]
    exact shiftedEraser _
  unfold groundBlock typedBlock groundGraph
  simp only [hl,hr,show da.2.2.2=SyntaxCode.typeCode τ from rfl,SyntaxCode.Proof.typeLevelExact,
    AbsoluteObserver.factor,MatrixCode.formula,MatrixCode.term,timesExact,eraserLift,
    CurrentUnitElimination.raw,MatrixCode.raw,variableIndex] <;> rfl

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.UnitCode
