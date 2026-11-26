module
public import LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedMatrixTargets
import LogicLineages.PermittedControl.OriginalNormalizedMatrixPositiveSnapshotsProof
import LogicLineages.PermittedControl.OriginalNormalizedMatrixPositiveSnapshotsShapeProof
import LogicLineages.PermittedControl.OriginalFieldGateMatrixRowProof
import LogicLineages.PermittedControl.ClosedOrdinaryFieldGuardProof
import LogicLineages.PermittedControl.AffineCollapseGuardRowsReadProof
import LogicLineages.PermittedControl.ThresholdNoteCodeProof
import LogicLineages.PermittedControl.PreparedParameterActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedMatrix
open OrdinalComparison FieldComparison PreparedProjection
open OriginalPrintedGreatestGateResolution (Mode)
open OriginalNormalizedCircuitMatrix (rows failedRows)
open OriginalFieldGateMatrix (equalityRow identityAffordRow)
open OriginalNormalizedMatrixPositiveSnapshots (oneEq threeTrueShape)
open HeterogeneousSignedMatrixSlice (actualRows)
open SignedRowSliceValue (valueAt)

private theorem shapeFlag (lam mu : NONote) :
    closedProperEntryGuard
      (rawNoteEncode lam.1,rawNoteEncode mu.1,rawNormCode (rawNoteEncode lam.1)) = true ↔
        ProperField (.entry 0 lam mu) := by
  have h := closedProperEntryDomainExact.2.2 lam mu (rawNormCode (rawNoteEncode lam.1))
  have norm := normal_norm_code lam
  change _ ↔ ProperField (.entry 0 lam mu) ∧
    actualOrdinalNorm lam.1.repr ≤ rawNormCode (rawNoteEncode lam.1) at h
  simpa only [norm,le_refl,and_true] using h

private theorem constantValue (f θ : Nat → Nat) (c v : Int) :
    valueAt f θ c [] v ↔ c = v := by
  constructor
  · rintro ⟨ys,live,eq⟩
    cases ys with
    | nil => simpa [MixedSameRankResidue.actualSum] using eq
    | cons y ys => exact False.elim live
  · intro eq
    exact ⟨[],True.intro,by simpa [MixedSameRankResidue.actualSum] using eq⟩

private theorem shapeValue (f θ : Nat → Nat) (lam mu : NONote) :
    valueAt f θ (shortShape lam mu).2.1 [] 0 ↔ ProperField (.entry 0 lam mu) := by
  rw [constantValue]
  have h := shapeFlag lam mu
  change (if closedProperEntryGuard
    (rawNoteEncode lam.1,rawNoteEncode mu.1,rawNormCode (rawNoteEncode lam.1)) then (0 : Int) else 1) = 0 ↔ _
  cases hguard : closedProperEntryGuard
    (rawNoteEncode lam.1,rawNoteEncode mu.1,rawNormCode (rawNoteEncode lam.1)) <;> simp_all

private theorem shortResult (f θ : Nat → Nat) (lam mu : NONote) (o : Nat) :
    valueAt f θ (shortValue lam mu o).2.1 (shortValue lam mu o).2.2 0 ↔
      θ o = shortGapLength lam mu := by
  change valueAt f θ (shortGapLength lam mu : Int)
    (([(-1,o)] : List (Int × Nat)).map (fun t => (t.1,.coordinate t.2))) 0 ↔ _
  rw [AffineCollapseGuardRows.coordinatesSum]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,neg_one_mul,add_zero]
  omega

private theorem afford (f θ : Nat → Nat) (lam : NONote) (s : Nat) (v : Int) :
    valueAt f θ (identityAffordRow lam s).2.1 (identityAffordRow lam s).2.2 v ↔
      (θ s : Int) - (actualOrdinalNorm lam.1.repr : Int) = v := by
  change valueAt f θ (-(actualOrdinalNorm lam.1.repr : Int))
    (([(1,s)] : List (Int × Nat)).map (fun t => (t.1,.coordinate t.2))) v ↔ _
  rw [AffineCollapseGuardRows.coordinatesSum]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,one_mul,add_zero]
  omega

private theorem shortRows (f θ : Nat → Nat) (lam mu : NONote) (s o : Nat) :
    PositiveRows f θ (emit (.shortCount lam mu s o)) ↔ (Mode.shortCount lam mu s o).Holds f θ := by
  constructor
  · rintro ⟨snap,reads,truth⟩
    obtain ⟨a,b,c,_,rawShape,rawAfford,rawValue⟩ :=
      threeTrueShape f θ (shortShape lam mu) (identityAffordRow lam s) (shortValue lam mu o) snap reads truth
    have sa : a = 0 := rawShape.2.2.1
    have sc : c = 0 := rawValue.2.2.1
    have nonneg : 0 ≤ b := rawAfford.2.2.1
    have eq := (afford f θ lam s b).mp rawAfford.2.1
    have paid : actualOrdinalNorm lam.1.repr ≤ θ s := by omega
    exact ⟨(shapeValue f θ lam mu).mp (sa ▸ rawShape.2.1),paid,
      (shortResult f θ lam mu o).mp (sc ▸ rawValue.2.1)⟩
  · rintro ⟨shape,paid,result⟩
    let v := (θ s : Int) - (actualOrdinalNorm lam.1.repr : Int)
    have nonneg : 0 ≤ v := by dsimp [v]; omega
    refine ⟨[(0,true),(v,true),(0,true)],?_,by simp [OriginalNormalizedMatrixPositiveSnapshots.AllTrue]⟩
    exact ⟨trivial,(shapeValue f θ lam mu).mpr shape,rfl,trivial,
      (afford f θ lam s v).mpr rfl,nonneg,trivial,(shortResult f θ lam mu o).mpr result,rfl,trivial⟩

private theorem keepOriginal (f θ : Nat → Nat) (g : OriginalPrintedCircuitNormalization.NormalizedGate) :
    PositiveRows f θ (rows g) ↔ g.graph f θ := by
  constructor
  · rintro ⟨values,live,truth⟩
    exact ((OriginalNormalizedMatrixPositiveSnapshots.exactPositiveCircuitSnapshots f θ [g] values).mp
      ⟨by simpa [OriginalNormalizedCircuitMatrix.rowsList] using live,truth⟩).1 g List.mem_cons_self
  · intro live
    let values := OriginalNormalizedCircuitMatrix.passing θ g
    have singleton : OriginalPrintedCircuitNormalization.Holds f θ [g] := by
      intro q hq
      have eq : q = g := List.mem_singleton.mp hq
      simpa only [eq] using live
    obtain ⟨reads,yes⟩ :=
      (OriginalNormalizedMatrixPositiveSnapshots.exactPositiveCircuitSnapshots f θ [g] values).mpr
        ⟨singleton,by simp [values,OriginalNormalizedCircuitMatrix.passingList]⟩
    exact ⟨values,by simpa [OriginalNormalizedCircuitMatrix.rowsList] using reads,yes⟩

private theorem iterateZero (f θ : Nat → Nat) (s o : Nat) :
    PositiveRows f θ [equalityRow (.coordinate s) o] ↔
      (OriginalNaturalFieldGates.Gate.iterate 0 s o).graph f θ := by
  have output := OriginalFieldGateMatrix.outputEquation f θ (.coordinate s) o
  have arithmetic : valueAt f θ 0 (equalityRow (.coordinate s) o).2.2 0 ↔ θ o = θ s :=
    output.trans (by simp [lowerOperandRead,eq_comm])
  have graph : (OriginalNaturalFieldGates.Gate.iterate 0 s o).graph f θ ↔ θ o = θ s := by
    change (True ∧ θ o = f^[0] (θ s)) ↔ _
    simp
  rw [graph]
  constructor
  · rintro ⟨snap,live,truth⟩
    have eq := oneEq f θ 0 (equalityRow (.coordinate s) o).2.2 snap live truth
    subst snap
    exact arithmetic.mp live.2.1
  · intro eq
    exact ⟨[(0,true)],⟨trivial,arithmetic.mpr eq,rfl,trivial⟩,
      by simp [OriginalNormalizedMatrixPositiveSnapshots.AllTrue]⟩

theorem exactModeMatrix : ExactModeMatrix := by
  intro f θ m
  cases m with
  | impossible =>
      refine ⟨?_,False.elim⟩
      rintro ⟨snap,live,truth⟩
      have eq := oneEq f θ 1 [] snap live truth
      subst snap
      have absurd := (constantValue f θ 1 0).mp live.2.1
      omega
  | shortCount lam mu s o => exact shortRows f θ lam mu s o
  | keep g =>
      cases g with
      | base g => exact keepOriginal f θ (.base g)
      | field g =>
          cases g with
          | iterate steps s o =>
              cases steps with
              | zero => exact iterateZero f θ s o
              | succ k => exact keepOriginal f θ (.field (.iterate (k+1) s o))
          | entry interval s o => exact keepOriginal f θ (.field (.entry interval s o))
          | count interval s o => exact keepOriginal f θ (.field (.count interval s o))

end LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedMatrix
