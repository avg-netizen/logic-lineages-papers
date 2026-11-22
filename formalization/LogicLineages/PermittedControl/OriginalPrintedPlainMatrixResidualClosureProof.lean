module
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixResidualClosureTargets
import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixResidualClosureSupportProof
import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixProjectedSupportProof
import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjectionProof
import LogicLineages.PermittedControl.OriginalMatrixLinearLowerTableProof
import LogicLineages.PermittedControl.OriginalProjectedMatrixDecodeProof
import LogicLineages.PermittedControl.OriginalProjectedMatrixSemanticsProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedPlainMatrixResidualClosure
open ActualFiniteOrderBranches (realized)
open OriginalMatrixLinearLowerTable (Live assignment exactLinearLowerTable)
open OriginalPrintedPlainMatrixProjectedSupport (argumentNames exactProjectedLowerSupport)
open OriginalPrintedPlainMatrixLinearProjection (table top safeMinimum formula replay exactAlreadyLinearCircuitProjection)
open OriginalPrintedPlainMatrixOrderBranches (renamed SourceAccepts)
open OriginalMatrixLowDimension (supportSet dimension)
open OriginalProjectedMatrixSemantics (availabilityRows MatrixAccepts exactResidualMatrixInterface)
open OriginalProjectedMatrixDecode (FitsOutput decode exactProjectedMatrixDecode)
open PreparedProjection (eliminatePreparedFormula PreparedTableTied)

theorem exactOriginalResidualMatrixClosure : ExactOriginalResidualMatrixClosure := by
  intro f θ B known gates p plain branch member checked nonempty linear prior positive fixedPrior
  let ranked := renamed known gates p branch
  let ρ := realized θ branch
  let ops := table known gates p branch
  let bound := safeMinimum B θ known gates p branch
  let q := formula known gates p branch bound positive
  let output := eliminatePreparedFormula q
  obtain ⟨plainOut,_,used,_,_,smaller,_,_⟩ :=
    exactProjectedLowerSupport f θ known gates p plain branch member checked nonempty linear bound positive
  have fit : FitsOutput ops output := by
    refine ⟨⟨plainOut,?_⟩,?_⟩
    · intro name hn
      obtain ⟨j,hj,eq,_⟩ := used name hn
      rw [eq]
      exact Nat.succ_le_of_lt hj
    · intro name hn
      obtain ⟨j,_,eq,_⟩ := used name hn
      rw [eq]
      exact Nat.succ_pos j
  obtain ⟨rows,decoded⟩ := exactProjectedMatrixDecode.2.2 ops output fit
  have support := residualArgumentNames ops output rows decoded
  have loss : dimension (availabilityRows ops ++ rows) < dimension ranked := by
    change (supportSet (availabilityRows ops ++ rows)).card < dimension ranked
    rw [support]
    exact smaller
  refine ⟨rows,decoded,support,loss,?_⟩
  have ties (live : Live f ρ ops) : PreparedTableTied f (top branch) ρ ops (assignment f ρ ops) :=
    (exactLinearLowerTable f ρ (top branch) ranked).2.2.1 live
  have residual : (Live f ρ ops ∧ output.eval (assignment f ρ ops)) ↔ MatrixAccepts f ρ ops output true rows :=
    exactResidualMatrixInterface f ρ (top branch) ops (assignment f ρ ops) output rows ties plainOut decoded true
  have source : (prior θ ∧ Live f ρ ops ∧ output.eval (assignment f ρ ops)) ↔
      ∃ z : Nat, bound ≤ z ∧ prior (replay θ known gates p branch z) ∧
        SourceAccepts f (replay θ known gates p branch z) known gates p positive :=
    exactAlreadyLinearCircuitProjection f θ B known gates p plain
      branch member checked nonempty linear prior positive fixedPrior
  exact (and_congr Iff.rfl residual.symm).trans source

end LogicLineages.PermittedControl.OriginalPrintedPlainMatrixResidualClosure
