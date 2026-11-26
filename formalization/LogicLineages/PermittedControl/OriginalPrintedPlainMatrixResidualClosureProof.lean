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
open PreparedProjection (LowerOperand PlainPreparedFormula eliminatePreparedFormula PreparedTableTied)
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open HeterogeneousSignedMatrixSlice (Row)

private theorem fitFromSlots (ops : List LowerOperand) (output : NormalForm.Formula)
    (plain : PlainPreparedFormula output)
    (slots : ∀ n ∈ output.variables, ∃ j : Fin ops.length, n = j.val+1) :
    FitsOutput ops output := by
  refine ⟨⟨plain,?_⟩,?_⟩
  · intro name hn
    obtain ⟨j,eq⟩ := slots name hn
    rw [eq]
    exact Nat.succ_le_of_lt j.isLt
  · intro name hn
    obtain ⟨j,eq⟩ := slots name hn
    rw [eq]
    exact Nat.succ_pos j.val

/-- Do not elaborate the existential over the source circuit AST when
composing the already checked returned-matrix interface. -/
private theorem closeResidual (f ρ ν : Nat → Nat) (z : Nat) (ranked : List Row)
    (ops : List LowerOperand) (output : NormalForm.Formula) (prior source : Prop)
    (fits : FitsOutput ops output)
    (ties : Live f ρ ops → PreparedTableTied f z ρ ops ν)
    (smaller : (argumentNames ops).card < dimension ranked)
    (projected : (prior ∧ Live f ρ ops ∧ output.eval ν) ↔ source) :
    ∃ rows : List Row, decode ops output = some rows ∧
      supportSet (availabilityRows ops ++ rows) = argumentNames ops ∧
      dimension (availabilityRows ops ++ rows) < dimension ranked ∧
      ((prior ∧ MatrixAccepts f ρ ops output true rows) ↔ source) := by
  obtain ⟨rows,decoded⟩ := exactProjectedMatrixDecode.2.2 ops output fits
  have support := residualArgumentNames ops output rows decoded
  have loss : dimension (availabilityRows ops ++ rows) < dimension ranked := by
    change (supportSet (availabilityRows ops ++ rows)).card < dimension ranked
    rw [support]
    exact smaller
  have semantics : (Live f ρ ops ∧ output.eval ν) ↔ MatrixAccepts f ρ ops output true rows :=
    exactResidualMatrixInterface f ρ z ops ν output rows ties fits.1.1 decoded true
  exact ⟨rows,decoded,support,loss,(and_congr Iff.rfl semantics.symm).trans projected⟩

theorem exactOriginalResidualMatrixClosure : ExactOriginalResidualMatrixClosure := by
  intro f θ B known gates p plain branch member checked nonempty linear prior positive fixedPrior
  let ranked := renamed known gates p branch
  let ρ := realized θ branch
  let ops := table known gates p branch
  let bound := safeMinimum B θ known gates p branch
  let q := formula known gates p branch bound positive
  let output := eliminatePreparedFormula q
  let source : Prop := ∃ z : Nat, bound ≤ z ∧ prior (replay θ known gates p branch z) ∧
    SourceAccepts f (replay θ known gates p branch z) known gates p positive
  have outFacts := exactProjectedLowerSupport f θ known gates p plain branch member checked nonempty linear bound positive
  have fits : FitsOutput ops output := by
    apply fitFromSlots ops output outFacts.1
    intro n hn
    obtain ⟨j,hj,eq,_⟩ := outFacts.2.2.1 n hn
    exact ⟨⟨j,hj⟩,eq⟩
  have ties (live : Live f ρ ops) : PreparedTableTied f (top branch) ρ ops (assignment f ρ ops) :=
    (exactLinearLowerTable f ρ (top branch) ranked).2.2.1 live
  have smaller : (argumentNames ops).card < dimension ranked := outFacts.2.2.2.2.2.1
  have projected : (prior θ ∧ Live f ρ ops ∧ output.eval (assignment f ρ ops)) ↔ source :=
    exactAlreadyLinearCircuitProjection f θ B known gates p plain
      branch member checked nonempty linear prior positive fixedPrior
  change ∃ rows : List Row, decode ops output = some rows ∧
    supportSet (availabilityRows ops ++ rows) = argumentNames ops ∧
    dimension (availabilityRows ops ++ rows) < dimension ranked ∧
    ((prior θ ∧ MatrixAccepts f ρ ops output true rows) ↔ source)
  exact closeResidual f ρ (assignment f ρ ops) (top branch) ranked ops output (prior θ) source
    fits ties smaller projected

end LogicLineages.PermittedControl.OriginalPrintedPlainMatrixResidualClosure
