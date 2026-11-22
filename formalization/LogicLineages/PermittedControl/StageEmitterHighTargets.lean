module
public import LogicLineages.PermittedControl.StageEmitterRowTargets
public import LogicLineages.PermittedControl.RawPacketAlgebraChildTargets
public import LogicLineages.PermittedControl.RawProperClauseTargets
public import LogicLineages.PermittedControl.ClosedBlockDecisionTargets

@[expose] public section
namespace LogicLineages.PermittedControl.StageEmitter
open StageCallbackRawLevel (Rendering rowCode)
open StageCallbackLevelOrder (levelOrder)
open StageCallbackSupplier (Emits)
open ClosedBlockDecision (ComputableEmitter ClosedBlockDecision)
open RawPacketAlgebra (childCode joinCode)
open RawProperClause (properClausesCode)
open ActualBitFamilyRawRank (familyCode)
open ActualBitFamilyRawLayout (RawFamily)
open ActualBitFamilyRawDriver (HighProgram)
open ActualFiniteOrderBranches (Pattern)
open OriginalPrintedPlainMatrixLinearProjection (top)

/-- One emitted child code per chart: raw rank renaming (#1298), the raw
proper-clause filter (#1393), the raw row program on every row of every kept
clause at the chart's width and greatest rank, the raw Cartesian join, and the
raw residual program (predecessor guard, projection, decode, reify). -/
def chartCode (R : Rendering) (C : Nat) (raw : RawFamily) (p : Pattern) : RawFamily :=
  childCode (C,top p,(properClausesCode (familyCode (p,raw))).flatMap
    (fun rows => joinCode (rows.map (rowCode R p.1 (top p)))))

/-- The assembled raw high program: one child per raw chart (#1311), in the
raw chart order, at the cutoff it is called with. -/
def highCode (R : Rendering) : HighProgram :=
  fun x => (ActualBitFamilyRawCharts.charts x.2).map (chartCode R x.1 x.2)

/-- Literal emission equation for the level-order supplier, every threshold,
from the calibration equations of the four rendering programs only. -/
def ExactStageEmission : Prop :=
  ∀ R : Rendering, R.Exact → ∀ B : Nat, Emits levelOrder B (highCode R)

/-- The assembled program is primitive recursive (hence computable) when its
four rendering programs are. -/
def ExactHighCodeEffectivity : Prop :=
  ∀ R : Rendering, RenderingEffective R → Primrec (highCode R) ∧ Computable (highCode R)

/-- Conditional close for every selected control. -/
def ExactConditionalEmitter : Prop :=
  ∀ R : Rendering, R.Exact → RenderingEffective R →
    ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B → ComputableEmitter f B

/-- Conditional close of the comparator of `thm:arithmetic`: one rendering
with exact calibrations and primitive recursive programs suffices. -/
def ExactConditionalClosedBlockDecision : Prop :=
  (∃ R : Rendering, R.Exact ∧ RenderingEffective R) → ClosedBlockDecision

def FullStageEmitterHigh : Prop :=
  ExactStageEmission ∧ ExactHighCodeEffectivity ∧ ExactConditionalEmitter ∧
    ExactConditionalClosedBlockDecision

end LogicLineages.PermittedControl.StageEmitter
