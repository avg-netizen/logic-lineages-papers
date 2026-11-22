module
public import LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedProjectionTargets
import LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedProjectionPreparedProof
import LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedProjectionDecreaseProof
import LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedProjectionProof
import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixResidualClosureSupportProof
import LogicLineages.PermittedControl.OriginalMatrixLinearLowerTableProof
import LogicLineages.PermittedControl.OriginalProjectedMatrixDecodeProof
import LogicLineages.PermittedControl.OriginalProjectedMatrixSemanticsProof
import LogicLineages.PermittedControl.PreparedParameterOutputProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedGreatestGateResolution (resolutionMinimum)
open OriginalPrintedPlainMatrixLinearProjection (top replay)
open OriginalPrintedPlainMatrixOrderBranches (renamed SourceAccepts)
open OriginalPrintedPlainMatrixResidualClosure (residualArgumentNames)
open OriginalPrintedPlainMatrixProjectedSupport (argumentNames)
open OriginalMatrixLowDimension (supportSet dimension)
open OriginalMatrixLinearLowerTable (Live assignment exactLinearLowerTable)
open OriginalProjectedMatrixSemantics (availabilityRows MatrixAccepts exactResidualMatrixInterface)
open OriginalProjectedMatrixDecode (FitsOutput decode exactProjectedMatrixDecode)
open PreparedProjection (LowerOperand PreparedInput eliminatePreparedFormula PreparedTableTied
  preparedProjectionSyntax)
open ActualFiniteOrderBranches (realized)
open HeterogeneousSignedMatrixSlice (Row)

private theorem fitsOfPrepared (ops : List LowerOperand) (q : NormalForm.Formula)
    (h : PreparedInput ops q) : FitsOutput ops (eliminatePreparedFormula q) := by
  have facts := preparedProjectionSyntax ops q h
  refine ⟨⟨facts.2.1,?_⟩,?_⟩
  · intro i hi
    exact (facts.2.2.2 i hi).2
  · intro i hi
    exact (facts.2.2.2 i hi).1

private theorem closeActual (f ρ ν : Nat → Nat) (z : Nat) (original : List Row)
    (ops : List LowerOperand) (out : NormalForm.Formula) (prior source : Prop)
    (fit : FitsOutput ops out)
    (tied : Live f ρ ops → PreparedTableTied f z ρ ops ν)
    (smaller : (argumentNames ops).card < dimension original)
    (projected : (prior ∧ Live f ρ ops ∧ out.eval ν) ↔ source) :
    ∃ rows : List Row, decode ops out = some rows ∧
      supportSet (availabilityRows ops ++ rows) = argumentNames ops ∧
      dimension (availabilityRows ops ++ rows) < dimension original ∧
      ((prior ∧ MatrixAccepts f ρ ops out true rows) ↔ source) := by
  obtain ⟨rows,decoded⟩ := exactProjectedMatrixDecode.2.2 ops out fit
  have names := residualArgumentNames ops out rows decoded
  have loss : dimension (availabilityRows ops ++ rows) < dimension original := by
    change (supportSet (availabilityRows ops ++ rows)).card < dimension original
    rw [names]
    exact smaller
  have semantics : (Live f ρ ops ∧ out.eval ν) ↔ MatrixAccepts f ρ ops out true rows :=
    exactResidualMatrixInterface f ρ z ops ν out rows tied fit.1.1 decoded true
  exact ⟨rows,decoded,names,loss,(and_congr Iff.rfl semantics.symm).trans projected⟩

theorem exactResolvedResidualClosure : ExactResolvedResidualClosure := by
  intro f B hf θ known gates p plain branch member ordered nonzero prior positive fixedPrior ops bound out
  let ρ := realized θ branch
  let z := top branch
  let q := formula known gates p branch bound positive
  let original := renamed known gates p branch
  let rs := ranked known gates p branch
  let ν := assignment f ρ ops
  let source : Prop := ∃ w : Nat, bound ≤ w ∧ prior (replay θ known gates p branch w) ∧
    SourceAccepts f (replay θ known gates p branch w) known gates p positive
  have shape : PreparedInput ops q :=
    (exactResolvedPrepared f θ known gates p plain branch member ordered bound positive).1
  have fit : FitsOutput ops out := fitsOfPrepared ops q shape
  have ties (live : Live f ρ ops) : PreparedTableTied f z ρ ops ν :=
    (exactLinearLowerTable f ρ z rs).2.2.1 live
  have smaller : (argumentNames ops).card < dimension original :=
    (exactResolvedProjectionDecrease θ known gates p branch member ordered nonzero).2
  have projected : (prior θ ∧ Live f ρ ops ∧ out.eval ν) ↔ source :=
    exactResolvedProjection f B hf θ known gates p plain branch member ordered prior positive fixedPrior
  change ∃ rows : List Row, decode ops out = some rows ∧
    supportSet (availabilityRows ops ++ rows) = argumentNames ops ∧
    dimension (availabilityRows ops ++ rows) < dimension original ∧
    ((prior θ ∧ MatrixAccepts f ρ ops out true rows) ↔ source)
  exact closeActual f ρ ν z original ops out (prior θ) source fit ties smaller projected

end LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedProjection
