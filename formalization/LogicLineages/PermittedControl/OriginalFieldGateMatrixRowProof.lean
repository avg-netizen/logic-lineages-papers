module
public import LogicLineages.PermittedControl.OriginalFieldGateMatrixTargets
import LogicLineages.PermittedControl.PreparedParameterActualProof
import LogicLineages.PermittedControl.AffineCollapseGuardRowsReadProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalFieldGateMatrix
open OrdinalComparison PreparedProjection
open MixedSameRankResidue (orderedReads actualSum)
open SignedRowSliceValue (valueAt)
open HeterogeneousSignedMatrixSlice (actualRows)

theorem outputEquation (f θ : Nat → Nat) (operand : LowerOperand) (out : Nat) :
    valueAt f θ 0 (equalityRow operand out).2.2 0 ↔
      lowerOperandRead f θ operand = some (some (θ out)) := by
  constructor
  · rintro ⟨ys,read,sum⟩
    rcases ys with _ | ⟨y,ys⟩
    · exact False.elim read
    rcases ys with _ | ⟨v,ys⟩
    · exact read.2.2.elim
    rcases ys with _ | ⟨a,ys⟩
    · have outValue : y = θ out := read.1
      have input : lowerOperandRead f θ operand = some (some v) := read.2.2.2.1
      change 0 + ((-1 : Int) * (y : Int) + (1 * (v : Int) + 0)) = 0 at sum
      simp only [neg_one_mul,one_mul,zero_add,add_zero] at sum
      have same : v = θ out := by omega
      rwa [same] at input
    · exact read.2.2.2.2.elim
  · intro hit
    refine ⟨[θ out,θ out],?_,?_⟩
    · exact ⟨rfl,rfl,(preparedTiedProjection.1 f θ operand (θ out)).mp hit,hit,trivial⟩
    · change 0 + ((-1 : Int) * (θ out : Int) + (1 * (θ out : Int) + 0)) = 0
      simp

theorem zeroEquation (f θ : Nat → Nat) (out : Nat) :
    valueAt f θ 0 (zeroRow out).2.2 0 ↔ θ out = 0 := by
  change valueAt f θ 0 ((([(-1,out)] : List (Int × Nat)).map
    (fun t => (t.1,.coordinate t.2)))) 0 ↔ _
  rw [AffineCollapseGuardRows.coordinatesSum]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,neg_one_mul,add_zero,zero_add]
  omega

theorem shapeValue (f θ : Nat → Nat) (mu : NONote) :
    valueAt f θ (identityShapeRow mu).2.1 [] 0 ↔
      terminalScanGuard (rawNoteEncode mu.1,rawNoteEncode mu.1) = true := by
  constructor
  · rintro ⟨ys,read,h⟩
    cases ys with
    | cons y ys => exact False.elim read
    | nil =>
        change (if terminalScanGuard (rawNoteEncode mu.1,rawNoteEncode mu.1) then (0 : Int)
          else 1) + 0 = 0 at h
        cases hguard : terminalScanGuard (rawNoteEncode mu.1,rawNoteEncode mu.1) <;> simp_all
  · intro h
    refine ⟨[],trivial,?_⟩
    change (if terminalScanGuard (rawNoteEncode mu.1,rawNoteEncode mu.1) then (0 : Int)
      else 1) + 0 = 0
    simp [h]

theorem affordableValue (f θ : Nat → Nat) (mu : NONote) (source : Nat) :
    valueAt f θ (identityAffordRow mu source).2.1 (identityAffordRow mu source).2.2
      ((θ source : Int)-(actualOrdinalNorm mu.1.repr : Int)) := by
  change valueAt f θ (-(actualOrdinalNorm mu.1.repr : Int))
    (([(1,source)] : List (Int × Nat)).map (fun t => (t.1,.coordinate t.2))) _
  apply (AffineCollapseGuardRows.coordinatesSum _ _ _ _ _).mpr
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,one_mul,add_zero]
  omega

end LogicLineages.PermittedControl.OriginalFieldGateMatrix
