module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphUnitCodeDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.Targets
open LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open AdmissibleSum

/-- Actual typed source/DAG renaming and Boolean lowering: raw operations
preserve the very same source payloads, literal rows and ordered prefix. -/
def ExactMatrixCodes : Prop :=
  (∀ (Γ Ξ : List Ty) (r : Renaming Γ Ξ) (t : SourceAST.Term Γ),
    MatrixCode.renameTerm (Ξ.map SyntaxCode.typeCode) (RawSourceDAG.Operations.renamingCode r)
      (MatrixCode.term t) = MatrixCode.term (CurrentUnitElimination.renameTerm r t)) ∧
  (∀ (Γ Ξ : List Ty) (r : Renaming Γ Ξ) (q : SourceAST.Formula Γ),
    MatrixCode.renameFormula (Ξ.map SyntaxCode.typeCode) (RawSourceDAG.Operations.renamingCode r)
      (MatrixCode.formula q) = MatrixCode.formula (CurrentUnitElimination.renameFormula r q)) ∧
  ∀ (Γ : List Ty) (q : SourceAST.Formula Γ),
    MatrixCode.inputCode (MatrixCode.formula q) = RawSourceDAG.InputCompiler.encodeInput q.toInput

noncomputable def codeUnitRender {Γ : List Ty} (p : Policy) (f : Nat → Nat)
    (a : CurrentUnitElimination.Tree Γ) : UnitCode.Block :=
  let b := CurrentUnitElimination.render p f a
  (b.width, MatrixCode.formula b.matrix)

/-- Literal same current selected elimination, not a check on extensionally
equivalent scalars. This equality includes fuel zero and all chosen branches;
a well-typed total witness follows from the already checked current437. -/
def ExactUnitBlock : Prop :=
  ∀ (p : Policy) (f : Nat → Nat) (fuel : Nat) (Γ : List Ty) (τ : Ty) (a : OriginalTerm Γ τ),
    UnitCode.blockFuel p f fuel (Γ.map SyntaxCode.typeCode) (SyntaxCode.encodeTerm a) =
      (CurrentUnitElimination.build p fuel a).map (codeUnitRender p f)

/-- Effective on raw encodings, without a classical lookup of a typed
compiled output. As with the source theorem, the computability of numeric
anchors is charged to the actual fixed f and actual effective policy. -/
def EffectiveMatrixUnitCodes : Prop :=
  Computable (fun d : List Nat × List Nat × Nat => MatrixCode.renameTerm d.1 d.2.1 d.2.2) ∧
  Computable (fun d : List Nat × List Nat × Nat => MatrixCode.renameFormula d.1 d.2.1 d.2.2) ∧
  Computable MatrixCode.inputCode ∧
  ∀ (p : Policy), PolicyShape.Effective p → ∀ (f : Nat → Nat),
    Computable f → FullAddition.Targets.SourceGrowth f →
    Computable (fun d : Nat × List Nat × Nat => UnitCode.blockFuel p f d.1 d.2.1 d.2.2) ∧
    Computable (fun d : List Nat × Nat => UnitCode.block p f d.1 d.2)

def UnitCodeSupport : Prop := ExactMatrixCodes ∧ ExactUnitBlock ∧ EffectiveMatrixUnitCodes

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.Targets
