module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphTemplateCodeProof
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphMatrixRowsProof
public import LogicLineages.ControlSensitivityCurrent.CurrentCompilerStatementChecks
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
open LogicLineages.OrdinalComparison.Source
open AdmissibleSum
open CurrentUnitElimination (WireCtx shift pinGround)
open RawSourceDAG (variableIndex)

private theorem pinSemantics (p : Policy) (f : Nat→Nat) (Γ : List Ty) {Δ : List Ty}
    (ρ : Variable Γ .ground→Nat) (ν : Variable Δ .ground→Nat)
    (r : Variable Γ .ground→Variable Δ .ground) :
    (pinGround Γ r ρ).eval p f ν=true ↔ ∀ x : Variable Γ .ground, ν (r x)=ρ x := by
  induction Γ with
  | nil =>
    constructor
    · intro _ x
      exact nomatch x
    · intro _
      rfl
  | cons σ Γ ih =>
    cases σ with
    | ground =>
      simp only [pinGround,SourceAST.Formula.eval,SourceAST.Term.eval,Bool.and_eq_true,
        decide_eq_true_eq,ih]
      refine ⟨fun h x => ?_,fun h => ⟨h .here,fun x => h (.there x)⟩⟩
      cases x with
      | here => exact h.1
      | there x => exact h.2 x
    | arrow a b =>
      rw [pinGround,ih]
      refine ⟨fun h x => ?_,fun h x => h (.there x)⟩
      cases x with
      | there x => exact h x

private theorem castHolds (p : Policy) (f : Nat→Nat) {Γ Δ : List Ty} (e : Γ=Δ)
    (q : SourceAST.Formula Γ) :
    (∃ ν : Variable Δ .ground→Nat, (e ▸ q : SourceAST.Formula Δ).eval p f ν=true) ↔
      ∃ ν : Variable Γ .ground→Nat, q.eval p f ν=true := by
  cases e; rfl

private theorem castFormulaCode {Γ Δ : List Ty} (e : Γ=Δ) (q : SourceAST.Formula Γ) :
    MatrixCode.formula (e ▸ q : SourceAST.Formula Δ)=MatrixCode.formula q := by cases e; rfl

private theorem externalLength {Γ : List Ty} (hg : ∀ σ ∈ Γ, σ=.ground) (ρ : Variable Γ .ground→Nat) :
    (externalValues ρ).length=Γ.length := by
  induction Γ with
  | nil => rfl
  | cons σ Γ ih =>
    obtain rfl := hg σ (by simp)
    simp only [externalValues,List.length_cons,ih (fun t ht => hg t (by simp [ht]))]

private theorem pinCodeExact {Γ Δ : List Ty} (hg : ∀ σ ∈ Γ, σ=.ground)
    (ρ : Variable Γ .ground→Nat) (r : Variable Γ .ground→Variable Δ .ground) (off : Nat)
    (h : ∀ x, variableIndex (r x)=off+variableIndex x) :
    MatrixCode.formula (pinGround Γ r ρ)=pinCode off (externalValues ρ) := by
  induction Γ generalizing off with
  | nil => rfl
  | cons σ Γ ih =>
    obtain rfl := hg σ (by simp)
    have ho : variableIndex (r .here)=off := by simpa only [variableIndex,Nat.add_zero] using h .here
    have hr (x : Variable Γ .ground) : variableIndex (r (.there x))=off+1+variableIndex x := by
      rw [h,variableIndex]
      omega
    rw [pinGround,externalValues,pinCode]
    simp only [MatrixCode.formula,MatrixCode.term,ho,ih (fun t ht => hg t (by simp [ht])) _ _ _ hr]

theorem exactFiberCompiler : Targets.ExactFiberCompiler := by
  intro p f hf Γ hg a ρ
  let s := closeAt a hg ρ
  have h : s.holds p f ↔ a.holds p f ρ := by
    unfold s closeAt SourceAST.Sentence.holds
    dsimp only
    rw [castHolds]
    simp only [Presented.holds,SourceAST.Formula.eval,Bool.and_eq_true,pinSemantics]
    exact exists_congr (fun ν => and_comm)
  have hcode : fiberInputCode (presentedCode a) (externalValues ρ) =
      (s.variables,RawSourceDAG.InputCompiler.encodeInput s.matrix.toInput) := by
    unfold fiberInputCode presentedCode s closeAt
    dsimp only
    rw [← MatrixCode.exactInputCode,castFormulaCode,widthLength,externalLength hg]
    have hp := pinCodeExact hg ρ (shift a.width) a.width (fun x => shiftedIndex a.width x)
    simp only [MatrixCode.formula,hp]
  have ho := CurrentCompiler.StatementChecks.fixed_complete_compiler.2.1.2 s
  have hm := CurrentCompiler.StatementChecks.fixed_complete_compiler.2.2.2.1 f hf p s
  refine ⟨h,hcode,?_,hm.1.trans (not_congr h),hm.2.trans (not_congr h)⟩
  unfold compiledFiberCode
  rw [hcode]
  exact ho

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
