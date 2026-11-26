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
  induction d <;> simp only [ScopedDAG.rename,prefixIdentity, *]

private theorem inputIdentity {Γ τ} (a : Input Γ τ) : ScopedDAG.renameInput (fun x => x) a=a := by
  cases a with
  | mk ss g r => simp only [ScopedDAG.renameInput,dagIdentity]

private theorem termId {Γ} (a : SourceAST.Term Γ) : renameTerm (fun x => x) a=a := by
  induction a <;> simp only [renameTerm,inputIdentity, *]

private theorem formulaId {Γ} (a : SourceAST.Formula Γ) : renameFormula (fun x => x) a=a := by
  induction a <;> simp only [renameFormula,termId, *]

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
  | succ n ih =>
    change MatrixCode.add (MatrixCode.term a) (MatrixCode.term (times n a)) =
      MatrixCode.add (MatrixCode.term a) (MatrixCode.times n (MatrixCode.term a))
    rw [ih]

theorem rowsExact {Γ} (row : LinearCode) (a b c : SourceAST.Term Γ) :
    MatrixCode.formula (rowFormula row a b c)=rawRow row (MatrixCode.term a) (MatrixCode.term b) (MatrixCode.term c) := by
  simp only [rowFormula,MatrixCode.formula,MatrixCode.term,timesExact,rawRow]

theorem underIndex {Γ Δ σ} (n : Nat) (r : Renaming Γ Δ) (k : Nat → Nat)
    (hr : ∀ {τ} (x : Variable Γ τ), variableIndex (r x)=k (variableIndex x))
    (x : Variable (WireCtx n Γ) σ) :
    variableIndex (under r n x) = if variableIndex x<n then variableIndex x else n+k (variableIndex x-n) := by
  induction n with
  | zero =>
    change variableIndex (r x) = if variableIndex x<0 then variableIndex x else 0+k (variableIndex x-0)
    rw [if_neg (Nat.not_lt_zero _),Nat.zero_add,Nat.sub_zero]
    exact hr x
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
  induction n generalizing Δ k with
  | zero =>
    cases x with
    | here => rfl
    | there x =>
      change variableIndex (r x) = if variableIndex x+1=0 then variableIndex z
        else k (if variableIndex x+1<0 then variableIndex x+1 else variableIndex x+1-1)
      rw [if_neg (Nat.add_one_ne_zero _),if_neg (Nat.not_lt_zero _),Nat.add_sub_cancel]
      exact hr x
  | succ n ih =>
    cases x with
    | here =>
      change variableIndex (r .here) = if 0=n+1 then _ else k (if 0<n+1 then 0 else 0-1)
      simpa only [Nat.zero_ne_add_one,Nat.zero_lt_succ,if_false,if_true,variableIndex] using hr .here
    | there x =>
      have ht (τ : Ty) (u : Variable (WireCtx n Γ) τ) :
          variableIndex (r (.there u))=k (variableIndex u+1) := hr (.there u)
      change variableIndex (reroute n (fun u => r (.there u)) z x) = _
      rw [ih (fun u => r (.there u)) z (fun j : Nat => k (j+1)) (fun x => ht _ x) x]
      simp only [variableIndex,Nat.add_right_cancel_iff,Nat.add_lt_add_iff_right,Nat.add_sub_cancel]
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
    rw [← tableByIndex _ (fun i => i+3) (fun x => by simp [variableIndex] <;> omega)]
  simp [shiftEraser,RawSourceDAG.encode,List.map_cons,SyntaxCode.typeCode,ht]

/-- Calibrate the two actual erasers separately before constructing the
unchanged source word. This keeps their scoped DAG reductions out of the
final structural matrix-code proof. -/
private theorem originalEraserExact {Γ : List Ty} {τ : Ty} (a : Input Γ τ) :
    originalEraser (encode ⟨Γ,τ,a⟩) = encode ⟨.ground::.ground::.ground::Γ,.ground,
      ScopedDAG.renameInput (eraserLift Γ) (AbsoluteProbeDAG.originalInput a)⟩ := by
  let Δ := Ty.ground::Ty.ground::Γ
  let d : Input Δ τ := ScopedDAG.renameInput (AbsoluteObserver.shiftTwo Γ) a
  have hs : MatrixCode.PrefixAt (AbsoluteObserver.shiftTwo Γ) 2 :=
    MatrixCode.prefixComp (MatrixCode.prefixOne Γ) (MatrixCode.prefixOne (.ground::Γ))
  have hl : CurrentDecisionEmitter.liftCode 2 (encode ⟨Γ,τ,a⟩) = encode ⟨Δ,τ,d⟩ :=
    MatrixCode.actualLift (AbsoluteObserver.shiftTwo Γ) 2 hs a
  have hp : CurrentProbeCode.probeRaw (encode ⟨Δ,τ,d⟩) 0 =
      encode ⟨Δ,.ground,AbsoluteProbeDAG.originalInput a⟩ :=
    CurrentProbeCode.exactProbe Δ τ d .here
  unfold originalEraser
  rw [hl,hp]
  exact shiftedEraser _

private theorem closedEraserExact {Γ : List Ty} {τ : Ty}
    (hg : ∀ σ ∈ Γ, σ = .ground) (a : Input Γ τ) :
    closedEraser (encode ⟨Γ,τ,a⟩) = encode ⟨.ground::.ground::.ground::Γ,.ground,
      ScopedDAG.renameInput (eraserLift Γ) (AbsoluteProbeDAG.closedInput hg a)⟩ := by
  let Δ := Ty.ground::Ty.ground::Γ
  let c : Input [] τ := AbsoluteProbeDAG.closeInput hg a
  let r : Renaming [] Δ := AbsoluteObserver.fromEmpty Δ
  let d : Input Δ τ := ScopedDAG.renameInput r c
  have hl : RawSourceDAG.Operations.renameCode (0::0::(encode ⟨Γ,τ,a⟩).1) []
      (CurrentProbeCode.closeRaw (encode ⟨Γ,τ,a⟩)) = encode ⟨Δ,τ,d⟩ := by
    rw [CurrentProbeCode.exactClosing Γ τ hg a]
    exact (RawSourceDAG.Operations.rename_input r c).symm
  have hp : CurrentProbeCode.probeRaw (encode ⟨Δ,τ,d⟩) 1 =
      encode ⟨Δ,.ground,AbsoluteProbeDAG.closedInput hg a⟩ :=
    CurrentProbeCode.exactProbe Δ τ d (.there .here)
  unfold closedEraser
  rw [hl,hp]
  exact shiftedEraser _

private theorem groundMatrixExact {Γ : List Ty}
    (l r : Input (.ground::.ground::.ground::Γ) .ground) (D c : Nat) :
    MatrixCode.formula (.conj (.eq (.observation l) (.observation r))
      (.eq (.add (times D (raw (.there (.there .here)))) (raw .here))
        (.add (.literal (D*c)) (raw (.there .here))))) =
    MatrixCode.both (MatrixCode.eq (MatrixCode.observe (encode ⟨_,.ground,l⟩))
      (MatrixCode.observe (encode ⟨_,.ground,r⟩)))
      (MatrixCode.eq (MatrixCode.add (MatrixCode.times D (MatrixCode.raw 2)) (MatrixCode.raw 0))
        (MatrixCode.add (MatrixCode.lit (D*c)) (MatrixCode.raw 1))) := by
  simp only [MatrixCode.formula,MatrixCode.term,timesExact,CurrentUnitElimination.raw,
    MatrixCode.raw,variableIndex] <;> rfl

section
attribute [local irreducible] originalEraser closedEraser CurrentAbsolute.anchor

theorem groundBlockExact (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ τ}
    (hg : ∀ σ ∈ Γ, σ = .ground) (a : Input Γ τ) :
    groundBlock p f (encode ⟨Γ,τ,a⟩)=typedBlock (groundGraph p f hg a) := by
  have hLevel : SyntaxCode.typeLevel (encode ⟨Γ,τ,a⟩).2.2.2=τ.level :=
    SyntaxCode.Proof.typeLevelExact τ
  unfold groundBlock typedBlock groundGraph
  dsimp only
  rw [originalEraserExact,closedEraserExact hg,hLevel]
  exact congrArg (fun v : Nat => (2,v))
    (groundMatrixExact (ScopedDAG.renameInput (eraserLift Γ) (AbsoluteProbeDAG.originalInput a))
      (ScopedDAG.renameInput (eraserLift Γ) (AbsoluteProbeDAG.closedInput hg a))
      (AbsoluteObserver.factor τ) (CurrentAbsolute.anchor p f (encode ⟨Γ,τ,a⟩))).symm

end

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.UnitCode
