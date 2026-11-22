module
public import LogicLineages.PermittedControl.ActualBitFamilyRawLowTargets
import LogicLineages.PermittedControl.ActualBitFamilyRawLayoutProof
import LogicLineages.PermittedControl.ActualBitFamilyLowSlicesProof
import LogicLineages.PermittedControl.SignedRowCoordinateSliceStatementChecks

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyRawLow
open HeterogeneousSignedMatrixSlice (Row encodeRow encodeTest sliceRows)
open SignedRowCoordinateSlice (slice encodeResidual)
open OriginalPrintedTerminalBitClauses (BitRow zipBits)
open ActualGuardedResidualBitFamily (Family)
open ActualBitFamilyLowSlices (sliceClause sliceFamily strips coordinates dimension
  originalRows wantedBits extractHits exactBitFamilyLowDimension)
open ActualBitFamilyRawLayout (encodeBitRow encodeFamily names exactRawFamilyNames)
open StatementChecks (fixed_signedRowCoordinateSliceCodeExact)
open MixedSameRankResidue (encodeWeighted)

theorem clauseCalibration (f : Nat → Nat) (name a : Nat) (clause : List BitRow) :
    clauseCode f (name,a,clause.map encodeBitRow) =
      (sliceClause f name a clause).map (List.map encodeBitRow) := by
  induction clause with
  | nil => rfl
  | cons h tail ih =>
      rcases h with ⟨⟨test,c,terms⟩,bit⟩
      let out := extractHits (sliceRows f name a (originalRows tail))
      have headEq :
          sliceOne f (name,a,encodeBitRow ((test,c,terms),bit)) =
            ((slice f name a c terms).bind id).map (fun r => encodeBitRow ((test,r),bit)) := by
        unfold sliceOne
        change takeHit ((encodeTest test,
          SignedRowCoordinateSlice.sliceCode f (name,a,c,terms.map encodeWeighted)),bit) = _
        rw [fixed_signedRowCoordinateSliceCodeExact.2]
        cases h : slice f name a c terms with
        | none => rfl
        | some p =>
            cases p with
            | none => rfl
            | some r => cases r; rfl
      change joinClause (sliceOne f (name,a,encodeBitRow ((test,c,terms),bit)))
        (clauseCode f (name,a,tail.map encodeBitRow)) = _
      rw [headEq,ih]
      change joinClause _ ((out.map (fun rs => zipBits rs (wantedBits tail))).map (List.map encodeBitRow)) =
        ((extractHits ((test,slice f name a c terms) :: sliceRows f name a (originalRows tail))).map
          (fun rows => zipBits rows (bit :: wantedBits tail))).map (List.map encodeBitRow)
      cases hs : slice f name a c terms with
      | none => rfl
      | some p =>
          cases p with
          | none => rfl
          | some r =>
              rcases r with ⟨b,ts⟩
              change joinClause (some (encodeBitRow ((test,b,ts),bit)))
                ((out.map (fun rs => zipBits rs (wantedBits tail))).map (List.map encodeBitRow)) =
                  ((out.map (List.cons (test,b,ts))).map
                    (fun rows => zipBits rows (bit :: wantedBits tail))).map (List.map encodeBitRow)
              cases h : out <;> rfl

theorem familyCalibration (f : Nat → Nat) (name a : Nat) (family : Family) :
    familyCode f (name,a,encodeFamily family) = encodeFamily (sliceFamily f name a family) := by
  induction family with
  | nil => rfl
  | cons head tail ih =>
      change
        (encodeFamily (head :: tail)).filterMap (fun c => clauseCode f (name,a,c)) =
          encodeFamily ((head :: tail).filterMap (sliceClause f name a))
      have ht :
          (encodeFamily tail).filterMap (fun c => clauseCode f (name,a,c)) =
            encodeFamily (tail.filterMap (sliceClause f name a)) := ih
      change
        ((head.map encodeBitRow :: encodeFamily tail).filterMap (fun c => clauseCode f (name,a,c))) =
          encodeFamily ((head :: tail).filterMap (sliceClause f name a))
      simp only [List.filterMap_cons, clauseCalibration]
      cases h : sliceClause f name a head with
      | none => simpa only [h, Option.map_none] using ht
      | some child =>
          simp only [h, Option.map_some]
          change child.map encodeBitRow ::
            ((encodeFamily tail).filterMap (fun c => clauseCode f (name,a,c))) =
              child.map encodeBitRow :: encodeFamily (tail.filterMap (sliceClause f name a))
          exact congrArg (List.cons (child.map encodeBitRow)) ht

theorem exactRawLowCalibration : ExactRawLowCalibration := by
  refine ⟨clauseCalibration,familyCalibration,?_⟩
  intro f name bound family
  simp only [stripsCode,strips,List.map_map,Function.comp_def,familyCalibration]

theorem exactRawLowDimension : ExactRawLowDimension := by
  intro f name bound family mem br hbr
  rw [exactRawLowCalibration.2.2] at hbr
  obtain ⟨typed,hTyped,rfl⟩ := List.mem_map.mp hbr
  have hf := exactRawFamilyNames.2 family
  have hc := exactRawFamilyNames.2 typed.2
  have used : name ∈ coordinates family := by
    rw [← hf.1]
    exact List.mem_toFinset.mpr mem
  have drop := exactBitFamilyLowDimension f name bound family used typed hTyped
  exact ⟨by simpa only [hf.1,hc.1] using drop.1,
    by simpa only [hf.2,hc.2] using drop.2⟩

end LogicLineages.PermittedControl.ActualBitFamilyRawLow
