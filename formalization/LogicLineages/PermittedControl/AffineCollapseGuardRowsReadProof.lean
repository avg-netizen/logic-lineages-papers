module
public import LogicLineages.PermittedControl.AffineCollapseGuardRowsTargets
import LogicLineages.PermittedControl.PreparedParameterActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.AffineCollapseGuardRows
open OrdinalComparison PreparedProjection FieldComparison
open MixedSameRankResidue (WeightedOperand orderedReads actualSum)
open SignedRowSliceValue (valueAt)

theorem coordinatesSum (f θ : Nat → Nat) (terms : List (Int × Nat)) (c v : Int) :
    valueAt f θ c (terms.map (fun t => (t.1,.coordinate t.2))) v ↔
      c + (terms.map (fun t => t.1 * (θ t.2 : Int))).sum = v := by
  have h : ∀ (ts : List (Int × Nat)) (ys : List Nat),
      orderedReads f θ (ts.map (fun t => (t.1,.coordinate t.2))) ys ↔
        ys = ts.map (fun t => θ t.2) := by
    intro ts
    induction ts with
    | nil =>
        intro ys
        cases ys <;> simp [orderedReads]
    | cons t ts ih =>
        intro ys
        cases ys with
        | nil => simp [orderedReads]
        | cons y ys =>
            simp only [List.map_cons,orderedReads,LowerOperandActual,lowerOperandRead,
              Option.some.injEq,List.cons.injEq,ih]
            constructor
            · rintro ⟨hy, _, hs⟩
              exact ⟨hy,hs⟩
            · rintro ⟨hy,hs⟩
              exact ⟨hy,hy.symm,hs⟩
  have hsum : ∀ ts : List (Int × Nat),
      actualSum (ts.map (fun t => (t.1,.coordinate t.2))) (ts.map (fun t => θ t.2)) =
        (ts.map (fun t => t.1 * (θ t.2 : Int))).sum := by
    intro ts
    induction ts with
    | nil => rfl
    | cons t ts ih =>
        change t.1 * (θ t.2 : Int) + actualSum
            (ts.map (fun t => (t.1,.coordinate t.2))) (ts.map (fun t => θ t.2)) =
          t.1 * (θ t.2 : Int) + (ts.map (fun t => t.1 * (θ t.2 : Int))).sum
        rw [ih]
  constructor
  · rintro ⟨ys,hy,hv⟩
    rw [(h terms ys).mp hy,hsum] at hv
    exact hv
  · intro hv
    refine ⟨_, (h terms _).mpr rfl, ?_⟩
    rw [hsum]
    exact hv

private theorem entryRead (f θ : Nat → Nat) (lam : NONote) (input : Nat) :
    lowerOperandRead f θ (.ordinary input (.entry 0 lam zeroTarget)) =
      (closedProperEntryResult f (rawNoteEncode lam.1,0,θ input)).map
        (Option.map Prod.fst) := by
  change (closedProperEntryResult f (rawNoteEncode lam.1,0,θ input)).map
    (fun r => r.map (fun hit => f^[0] hit.1)) = _
  simp only [Function.iterate_zero, id_eq] <;> rfl

private theorem countRead (f θ : Nat → Nat) (lam : NONote) (input : Nat) :
    lowerOperandRead f θ (.count input lam zeroTarget) =
      (closedProperEntryResult f (rawNoteEncode lam.1,0,θ input)).map
        (Option.map Prod.snd) := rfl

theorem collapseValue (f θ : Nat → Nat) (lam : NONote) (input output : Nat) (v : Int) :
    valueAt f θ 0 (collapseTerms lam input output) v ↔
      ∃ h : Nat × Nat,
        closedProperEntryResult f (rawNoteEncode lam.1,0,θ input) = some (some h) ∧
          (h.1 : Int) + (h.2 : Int) - (θ output : Int) = v := by
  let R := closedProperEntryResult f (rawNoteEncode lam.1,0,θ input)
  have rw_entry := entryRead f θ lam input
  have rw_count := countRead f θ lam input
  change _ = R.map (Option.map Prod.fst) at rw_entry
  change _ = R.map (Option.map Prod.snd) at rw_count
  change _ ↔ ∃ h : Nat × Nat, R = some (some h) ∧ _
  constructor
  · rintro ⟨ys,hy,hv⟩
    rcases ys with _ | ⟨y,ys⟩
    · exact False.elim hy
    rcases ys with _ | ⟨en,ys⟩
    · exact hy.2.2.elim
    rcases ys with _ | ⟨k,ys⟩
    · exact hy.2.2.2.2.elim
    rcases ys with _ | ⟨a,ys⟩
    · have hy₀ : y = θ output := hy.1
      have he := hy.2.2.2.1
      have hk := hy.2.2.2.2.2.1
      change lowerOperandRead f θ (.ordinary input (.entry 0 lam zeroTarget)) =
        some (some en) at he
      change lowerOperandRead f θ (.count input lam zeroTarget) = some (some k) at hk
      rw [rw_entry] at he
      rw [rw_count] at hk
      cases hg : R with
      | none => simp [hg] at he
      | some s =>
          cases s with
          | none => simp [hg] at he
          | some hit =>
              have hen : hit.1 = en := by simpa [hg] using he
              have hkn : hit.2 = k := by simpa [hg] using hk
              refine ⟨hit,rfl,?_⟩
              change 0 + ((-1 : Int) * (y : Int) +
                (1 * (en : Int) + (1 * (k : Int) + 0))) = v at hv
              simp only [neg_one_mul,one_mul,zero_add,add_zero] at hv
              omega
    · exact hy.2.2.2.2.2.2.elim
  · rintro ⟨hit,hR,hv⟩
    have he : lowerOperandRead f θ (.ordinary input (.entry 0 lam zeroTarget)) =
        some (some hit.1) := by rw [rw_entry,hR] <;> rfl
    have hk : lowerOperandRead f θ (.count input lam zeroTarget) =
        some (some hit.2) := by rw [rw_count,hR] <;> rfl
    refine ⟨[θ output,hit.1,hit.2], ?_, ?_⟩
    · exact ⟨rfl,rfl,(preparedTiedProjection.1 _ _ _ _).mp he,he,
        (preparedTiedProjection.1 _ _ _ _).mp hk,hk,trivial⟩
    · change 0 + ((-1 : Int) * (θ output : Int) +
        (1 * (hit.1 : Int) + (1 * (hit.2 : Int) + 0))) = v
      simp only [neg_one_mul,one_mul,zero_add,add_zero]
      omega

end LogicLineages.PermittedControl.AffineCollapseGuardRows
