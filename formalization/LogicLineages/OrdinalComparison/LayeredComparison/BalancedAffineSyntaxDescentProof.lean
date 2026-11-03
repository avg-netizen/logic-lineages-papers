module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedAffineSyntaxClosureProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedCollectionProof
public import Mathlib.Tactic.Ring
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedSyntax.Affine.Proof

private theorem affineZipNatCast (rs : List Int) (bs : List Nat) :
    rs.zipWith (fun r b => r*(b:Int)) bs =
      rs.zipWith (fun (r:Int) (b:Nat) => r*(b:Int)) bs := by
  induction rs generalizing bs with
  | nil => rfl
  | cons r rs ih =>
    cases bs with
    | nil => rfl
    | cons b bs =>
      change r*(b:Int)::(rs.zipWith (fun r b => r*(b:Int)) bs) =
        r*(b:Int)::(rs.zipWith (fun (r:Int) (b:Nat) => r*(b:Int)) bs)
      rw [ih]

private theorem affineCastSumOfFn (k : Nat) : ∀ f : Fin k → Nat,
    ((List.ofFn f).sum:Int) = (List.ofFn (fun j => (f j:Int))).sum := by
  induction k with
  | zero => intro f; rfl
  | succ k ih =>
    intro f
    rw [List.ofFn_succ, List.ofFn_succ]
    simp only [List.sum_cons, Nat.cast_add, ih]

private theorem affineSubSumOfFn (k : Nat) : ∀ f g : Fin k → Int,
    (List.ofFn (fun j => f j-g j)).sum = (List.ofFn f).sum-(List.ofFn g).sum := by
  induction k with
  | zero => intro f g; rfl
  | succ k ih =>
    intro f g
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
    simp only [List.sum_cons, ih]
    ring

private theorem affineOutsideDifference {k : Nat} (a b v : Fin k → Nat) :
    ((List.ofFn (fun j => (a j:Int)-(b j:Int))).zipWith
      (fun (r:Int) (x:Nat) => r*(x:Int)) (List.ofFn v)).sum =
      (((List.ofFn a).zipWith (fun (x y:Nat) => (x*y:Nat)) (List.ofFn v)).sum:Int)-
      (((List.ofFn b).zipWith (fun (x y:Nat) => (x*y:Nat)) (List.ofFn v)).sum:Int) := by
  rw [affineZipOfFn, affineZipOfFn, affineZipOfFn, affineCastSumOfFn, affineCastSumOfFn]
  have ht : (fun j : Fin k => ((a j:Int)-(b j:Int))*(v j:Int)) =
      (fun j => ((a j*v j:Nat):Int)-((b j*v j:Nat):Int)) := by
    funext j
    simp only [Nat.cast_mul]
    ring
  simpa only [ht, affineSubSumOfFn]

private theorem affineCastSumMap {A : Type} (xs : List A) (f : A → Nat) :
    ((xs.map f).sum:Int) = (xs.map (fun a => (f a:Int))).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]

private theorem affineNegSumMap {A : Type} (xs : List A) (f : A → Int) :
    (xs.map (fun a => -(f a))).sum = -(xs.map f).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.map_cons, List.sum_cons, ih, neg_add]

private theorem affineCastHeadSum {k : Nat} (E : Upper k) (basis : List Nat) :
    ((E.atoms.map (fun a => (a.1+1)*actualHeadValue a.2.head.1.repr
      (BalancedRow.input basis (asAtom a.2)))).sum:Int) =
    (E.atoms.map (fun a => (a.1+1:Int)*(actualHeadValue a.2.head.1.repr
      (BalancedRow.input basis (asAtom a.2)):Int))).sum := by
  rw [affineCastSumMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]

private theorem affineAtomHead {k : Nat} (a : Atom k) : (asAtom a).head = a.head := rfl

/-- Direct calibration of the frozen literal source row, using only its list
arithmetic rather than the unrelated program-interface import closure. -/
private theorem affineComparisonRow (k : Nat) (Γ : List Nat) (C : Certificate (k::Γ))
    (E F : Upper k) (ν : Nat → Nat) :
    BalancedRow.value (basisValues k Γ C ν) (comparisonRow E F) =
      (value (k::Γ) C E ν:Int)-(value (k::Γ) C F ν:Int) := by
  simp only [value, basisValues]
  unfold BalancedRow.value BalancedRow.remainderValue comparisonRow
  rw [affineZipNatCast, affineOutsideDifference]
  simp only [List.map_append, List.map_map, List.sum_append, Function.comp_def,
    affineAtomHead, neg_mul]
  rw [affineNegSumMap]
  simp only [Nat.cast_add]
  rw [affineCastHeadSum, affineCastHeadSum]
  ring

/-- The literal outside term is evaluated under the original lower certificate. -/
theorem value_lowerPart (k : Nat) (Γ : List Nat) (C : Certificate (k::Γ))
    (E : Upper k) (ν : Nat → Nat) :
    value Γ C.1 (lowerPart k Γ C E) ν =
      E.constant + ((List.ofFn E.outside).zipWith (·*·) (basisValues k Γ C ν)).sum := by
  simpa only [lowerPart, basisValues] using
    value_combination Γ C.1 k E.constant E.outside C.2 ν

/-- The complete argument includes the actual head norm and every positive
coefficient of the same ordered basis, even when that basis has repetitions. -/
theorem value_completeInput (k : Nat) (Γ : List Nat) (C : Certificate (k::Γ))
    (a : Atom k) (ν : Nat → Nat) :
    value Γ C.1 (completeInput k Γ C a) ν =
      BalancedRow.input (basisValues k Γ C ν) (asAtom a) := by
  simpa only [completeInput, basisValues, BalancedRow.input, BalancedRow.normOffset,
    asAtom] using
    value_combination Γ C.1 k (actualOrdinalNorm a.head.1.repr + a.offset)
      (fun j => a.factors j + 1) C.2 ν

theorem actualLowerAndInputs : Targets.ActualLowerAndInputs := by
  intro k Γ C E a ν
  refine ⟨value_lowerPart k Γ C E ν, value_completeInput k Γ C a ν, ?_, ?_, ?_⟩
  · intro i
    exact mem_rawVariables_combination Γ C.1 k E.constant E.outside C.2 i
  · intro i
    change i ∈ rawVariables Γ C.1
      (combination Γ k (actualOrdinalNorm a.head.1.repr + a.offset)
        (fun j => a.factors j + 1) C.2) ↔ _
    rw [mem_rawVariables_combination]
    constructor
    · rintro ⟨j, _, hj⟩
      exact ⟨j, hj⟩
    · rintro ⟨j, hj⟩
      exact ⟨j, Nat.succ_ne_zero _, hj⟩
  · intro hC
    exact ⟨genuine_combination Γ k E.constant E.outside C.2 hC.2,
      genuine_combination Γ k (actualOrdinalNorm a.head.1.repr + a.offset)
        (fun j => a.factors j + 1) C.2 hC.2⟩

/-- Collection cancels heads without replacing the actual lower source terms
by independent values. The entire signed remainder has their exact difference. -/
theorem actualCanceledDescent : Targets.ActualCanceledDescent := by
  intro k Γ C E F ν hc
  have hrow := affineComparisonRow k Γ C E F ν
  have hcancel := (BalancedRow.Collection.Proof.exactCollectedValue
    (basisValues k Γ C ν) (comparisonRow E F)).2.2.2.2 hc
  calc
    (value (k::Γ) C E ν : Int) - (value (k::Γ) C F ν : Int) =
        BalancedRow.value (basisValues k Γ C ν) (comparisonRow E F) := hrow.symm
    _ = BalancedRow.remainderValue (basisValues k Γ C ν) (comparisonRow E F) := hcancel
    _ = (value Γ C.1 (lowerPart k Γ C E) ν : Int) -
        (value Γ C.1 (lowerPart k Γ C F) ν : Int) := by
      rw [value_lowerPart, value_lowerPart]
      simp only [BalancedRow.remainderValue, comparisonRow, basisValues]
      rw [affineZipNatCast, affineOutsideDifference]
      simp only [Nat.cast_add]
      ring

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedSyntax.Affine.Proof
