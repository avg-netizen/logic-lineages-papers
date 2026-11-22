module
public import LogicLineages.PermittedControl.OriginalPrintedGreatestGateResolutionTargets
import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjectionReplayProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesRealizationProof
import LogicLineages.PermittedControl.OriginalMatrixUniformHighBoundProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedGreatestGateResolution
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitNormalization (NormalizedGate)
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedPlainMatrixInfiniteLow (matrix circuit)
open OriginalPrintedPlainMatrixOrderBranches (branches)
open OriginalPrintedPlainMatrixLinearProjection (top replay safeMinimum exactGreatestReplayGuards)
open OriginalMatrixDenseRanks (support)
open OriginalNormalizedCircuitMatrix (rows rowsList LimitHead baseRows limitRows)
open ActualFiniteOrderBranches (Pattern rename guard exactBranchRealization)
open HeterogeneousSignedMatrixSlice (Row)

theorem boundAt (gs : List NormalizedGate) (g : NormalizedGate) (h : g ∈ gs) :
    gateBound g ≤ familyBound gs :=
  OriginalMatrixUniformHighBound.foldCeilingBound gateBound gs g h

private theorem gateSupport (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (g : NormalizedGate) (h : g ∈ circuit known gates p) (name : Nat)
    (inGate : name ∈ support (rows g)) : name ∈ support (matrix known gates p) := by
  obtain ⟨r,atRow,hasName⟩ := List.mem_flatMap.mp inGate
  have hr : r ∈ rowsList (circuit known gates p) := List.mem_flatMap.mpr ⟨g,h,atRow⟩
  exact List.mem_flatMap.mpr ⟨r,List.mem_append_left _ hr,hasName⟩

theorem fieldSupport (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (g : OriginalNaturalFieldGates.Gate) (listed : NormalizedGate.field g ∈ circuit known gates p) :
    g.source ∈ support (matrix known gates p) ∧ g.output ∈ support (matrix known gates p) := by
  have localNames : g.source ∈ support (rows (.field g)) ∧ g.output ∈ support (rows (.field g)) := by
    cases g with
    | iterate a s o =>
        simp [rows,OriginalFieldGateMatrix.rows,OriginalFieldGateMatrix.equalityRow,
          OriginalNaturalFieldGates.Gate.source,OriginalNaturalFieldGates.Gate.output,support,PreparedProjection.LowerOperand.rank]
    | entry interval s o =>
        cases interval <;>
          simp [rows,OriginalFieldGateMatrix.rows,OriginalFieldGateMatrix.equalityRow,
            OriginalFieldGateMatrix.identityShapeRow,OriginalFieldGateMatrix.identityAffordRow,
            OriginalNaturalFieldGates.Gate.source,OriginalNaturalFieldGates.Gate.output,support,PreparedProjection.LowerOperand.rank]
    | count interval s o =>
        cases interval <;>
          simp [rows,OriginalFieldGateMatrix.rows,OriginalFieldGateMatrix.equalityRow,
            OriginalFieldGateMatrix.identityShapeRow,OriginalFieldGateMatrix.identityAffordRow,OriginalFieldGateMatrix.zeroRow,
            OriginalNaturalFieldGates.Gate.source,OriginalNaturalFieldGates.Gate.output,support,PreparedProjection.LowerOperand.rank]
  exact ⟨gateSupport known gates p (.field g) listed g.source localNames.1,
    gateSupport known gates p (.field g) listed g.output localNames.2⟩

theorem limitSupport (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (head : Nat) (e : NaturalAffineGateGraph.Expression) (s o : Nat) (typed : LimitHead head)
    (listed : NormalizedGate.base (.limitPair head e s o) ∈ circuit known gates p) :
    s ∈ support (matrix known gates p) ∧ o ∈ support (matrix known gates p) := by
  refine ⟨gateSupport known gates p (.base (.limitPair head e s o)) listed s ?_,
    gateSupport known gates p (.base (.limitPair head e s o)) listed o ?_⟩ <;>
    simp [rows,baseRows,limitRows,typed,support,AffineCollapseGuardRows.guardRows,
      AffineCollapseGuardRows.affineTerms,AffineCollapseGuardRows.collapseTerms,
      PreparedProjection.LowerOperand.rank]

/-- Derive the numeric comparison only from the actual two literal
support occurrences and the actual preserved initial order branch. -/
theorem maximalInput (B : Nat) (θ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula) (branch : Pattern) (member : branch ∈ branches known gates p)
    (checked : (guard branch).eval θ) (z : Nat)
    (paid : safeMinimum B θ known gates p branch ≤ z) (s o : Nat)
    (liveS : s ∈ support (matrix known gates p)) (liveO : o ∈ support (matrix known gates p))
    (atTop : rename branch s = top branch) :
    replay θ known gates p branch z o ≤ replay θ known gates p branch z s ∧
      replay θ known gates p branch z s = z := by
  let ν := replay θ known gates p branch z
  have actualGuard := (exactGreatestReplayGuards B θ known gates p branch member checked z paid).1
  obtain ⟨strict,_,ties⟩ := exactBranchRealization ν (support (matrix known gates p)) branch member actualGuard
  have le : rename branch o ≤ top branch := Nat.le_pred_of_lt (ties o liveO).1
  have cmp := strict.monotone (show rename branch o ≤ rename branch s by rwa [atTop])
  rw [(ties o liveO).2,(ties s liveS).2] at cmp
  exact ⟨cmp,by simp [ν,replay,liveS,atTop]⟩

end LogicLineages.PermittedControl.OriginalPrintedGreatestGateResolution
