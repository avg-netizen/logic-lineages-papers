module
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjectionTargets
public import LogicLineages.PermittedControl.OriginalMatrixLowDimensionTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedPlainMatrixProjectedSupport
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedPlainMatrixOrderBranches (branches renamed)
open OriginalPrintedPlainMatrixLinearProjection (table formula top)
open OriginalMatrixLinearLowerTable (TopLinear)
open OriginalMatrixLowDimension (supportSet dimension)
open ActualFiniteOrderBranches (Pattern guard realized)
open PreparedProjection (LowerOperand PlainPreparedFormula eliminatePreparedFormula
  eliminatePreparedCode preparedPacketCode PreparedTableTied lowerOperandRead)

def argumentNames (ops : List LowerOperand) : Finset Nat := (ops.map LowerOperand.rank).toFinset

/-- Support includes the *entire* retained actual lower tape, so even
the availability guard for unused preserved table slots only consults
strictly lower ranks. Arbitrary outer priors are not counted. -/
def ExactProjectedLowerSupport : Prop :=
  ∀ (f θ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula),
    PlainPreparedFormula p →
    ∀ branch ∈ branches known gates p, (guard branch).eval θ → 0 < branch.1 →
      TopLinear (top branch) (renamed known gates p branch) →
      ∀ (minimum : Nat) (positive : Bool),
        let ranked := renamed known gates p branch
        let ops := table known gates p branch
        let q := formula known gates p branch minimum positive
        let output := eliminatePreparedFormula q
        PlainPreparedFormula output ∧
        (∀ name : Nat, name ∈ output.variables ↔ name ≠ 0 ∧ name ∈ q.variables) ∧
        (∀ name ∈ output.variables, ∃ j : Nat, ∃ hj : j < ops.length,
          name = j+1 ∧ (ops[j]).rank < top branch) ∧
        (∀ op ∈ ops, ∃ row ∈ ranked, ∃ t ∈ row.2.2,
          t.2 = op ∧ op.rank < top branch) ∧
        argumentNames ops ⊆ (supportSet ranked).erase (top branch) ∧
        (argumentNames ops).card < dimension ranked ∧
        eliminatePreparedCode (preparedPacketCode ops q) = preparedPacketCode ops output ∧
        ∀ (ν : Nat → Nat), PreparedTableTied f (top branch) (realized θ branch) ops ν →
          ∀ name ∈ output.variables, ∃ j : Nat, ∃ hj : j < ops.length,
            name = j+1 ∧
            lowerOperandRead f (realized θ branch) ops[j] = some (some (ν name)) ∧
            ∀ value : Nat,
              lowerOperandRead f (Function.update (realized θ branch) (top branch) value) ops[j] =
                some (some (ν name))

end LogicLineages.PermittedControl.OriginalPrintedPlainMatrixProjectedSupport
