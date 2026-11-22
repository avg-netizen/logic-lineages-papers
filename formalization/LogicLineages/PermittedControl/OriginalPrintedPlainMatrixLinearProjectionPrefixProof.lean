module
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjectionTargets
import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjectionSyntaxProof
import LogicLineages.PermittedControl.OriginalNormalizedMatrixPositiveSnapshotsShapeProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitNormalization (NormalizedGate)
open OriginalNormalizedCircuitMatrix (rows rowsList baseRows limitRows LimitHead typedHead)
open OriginalNormalizedMatrixPositiveSnapshots (AllTrue)
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)
open SignedRowGuardedTest (Test)

private def admission (test : Test) : Bool :=
  match test with
  | .congruence m => decide (0 < m)
  | _ => true

private theorem admitted (r : Row) (h : admission r.1 = true) : r.1.Admitted := by
  rcases r with ⟨test,c,ts⟩
  cases test with
  | equalZero => trivial
  | nonnegative => trivial
  | positive => trivial
  | congruence m =>
      change 0 < m
      exact decide_eq_true_eq.mp (show decide (0 < m) = true from h)

private theorem admitsGate (g : NormalizedGate) : (rows g).all (fun r => admission r.1) = true := by
  cases g with
  | base g =>
      cases g with
      | affine e o => rfl
      | limitPair h e i o =>
          by_cases typed : LimitHead h
          · simp only [rows,baseRows,limitRows,dif_pos typed] <;> rfl
          · simp only [rows,baseRows,limitRows,dif_neg typed] <;> rfl
  | field g =>
      cases g with
      | iterate n s o => rfl
      | entry interval s o => cases interval <;> rfl
      | count interval s o => cases interval <;> rfl

theorem admitsPrefix (gs : List NormalizedGate) (r : Row) (member : r ∈ rowsList gs) : r.1.Admitted := by
  obtain ⟨g,_,hr⟩ := List.mem_flatMap.mp member
  exact admitted r (List.all_eq_true.mp (admitsGate g) r hr)

theorem admitsAtom (a : NormalForm.Atom) : (OriginalPlainTerminalMatrix.atomRow a).1.Admitted := by
  cases a with
  | nonnegative _ => trivial
  | divisible m _ => exact Nat.succ_pos m

theorem truePrefix (f θ ν : Nat → Nat) (rs : List Row) (emit : Row → NormalForm.Formula)
    (meaning : ∀ r ∈ rs, (emit r).eval ν ↔ ∃ v : Int, actualRows f θ [r] [(v,true)]) :
    (conjoin (rs.map emit)).eval ν ↔ ∃ snap : Snapshot, actualRows f θ rs snap ∧ AllTrue snap := by
  induction rs with
  | nil =>
      constructor
      · intro _
        exact ⟨[],True.intro,by simp [AllTrue]⟩
      · intro _
        exact True.intro
  | cons r rs ih =>
      have tail := ih (fun r hr => meaning r (List.mem_cons_of_mem _ hr))
      have head := meaning r List.mem_cons_self
      change ((emit r).eval ν ∧ (conjoin (rs.map emit)).eval ν) ↔ _
      constructor
      · rintro ⟨h,t⟩
        obtain ⟨v,live⟩ := head.mp h
        obtain ⟨snap,rest,yes⟩ := tail.mp t
        refine ⟨(v,true) :: snap,⟨live.1,live.2.1,live.2.2.1,rest⟩,?_⟩
        exact (OriginalNormalizedMatrixPositiveSnapshots.allAppend [(v,true)] snap).mpr
          ⟨by simp [AllTrue],yes⟩
      · rintro ⟨snap,live,yes⟩
        cases snap with
        | nil => exact False.elim live
        | cons v vs =>
            have vTrue := yes v List.mem_cons_self
            have headLive : actualRows f θ [r] [v] := ⟨live.1,live.2.1,live.2.2.1,True.intro⟩
            refine ⟨head.mpr ⟨v.1,(Prod.ext rfl vTrue : v = (v.1,true)) ▸ headLive⟩,?_⟩
            exact tail.mpr ⟨vs,live.2.2.2,fun t ht => yes t (List.mem_cons_of_mem _ ht)⟩

end LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjection
