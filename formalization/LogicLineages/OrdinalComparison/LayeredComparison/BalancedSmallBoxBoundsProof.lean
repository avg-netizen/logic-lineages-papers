module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedSmallBoxSupportProof
public import LogicLineages.OrdinalComparison.LayeredComparison.HeterogeneousHeadProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBasisProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedSmallBox.Proof
open BalancedSyntax

private theorem sum_member {xs : List Nat} {x : Nat} (hx : x ∈ xs) : x ≤ xs.sum := by
  induction xs with
  | nil => cases hx
  | cons a xs ih =>
    rcases List.mem_cons.mp hx with h | h
    · subst x; simp only [List.sum_cons]; omega
    · have ht := ih h; simp only [List.sum_cons]; omega

theorem atomShape (k : Nat) (Γ : List Nat) (C : Certificate (k :: Γ))
    (ν : Nat → Nat) (a : Atom k) :
    (asAtom a).coefficients.length = (basisValues k Γ C ν).length ∧
      ∀ c ∈ (asAtom a).coefficients, 1 ≤ c := by
  constructor
  · simp [asAtom, basisValues]
  · intro c hc
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc
    omega

theorem rowWellFormed (k : Nat) (Γ : List Nat) (C : Certificate (k :: Γ))
    (E F : Upper k) (ν : Nat → Nat) :
    BalancedRow.wellFormed (basisValues k Γ C ν) (comparisonRow E F) := by
  constructor
  · simp [comparisonRow, basisValues]
  · intro a ha
    rcases List.mem_append.mp ha with he | hf
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp he
      exact atomShape k Γ C ν b.2
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hf
      exact atomShape k Γ C ν b.2

private theorem outside_le_value {k : Nat} {Γ : List Nat} (C : Certificate (k :: Γ))
    (E : Upper k) (ν : Nat → Nat) (j : Fin k) :
    E.outside j * value Γ C.1 (C.2 j) ν ≤ value (k :: Γ) C E ν := by
  have hm : E.outside j * value Γ C.1 (C.2 j) ν ∈
      (List.ofFn E.outside).zipWith (· * ·) (basisValues k Γ C ν) := by
    rw [basisValues, Affine.Proof.affineZipOfFn]
    exact List.mem_ofFn.mpr ⟨j, rfl⟩
  have hs := sum_member hm
  simp only [value, basisValues] at hs ⊢
  omega

private theorem head_le_value {k : Nat} {Γ : List Nat} (C : Certificate (k :: Γ))
    (E : Upper k) (ν : Nat → Nat) (a : Nat × Atom k) (ha : a ∈ E.atoms) :
    actualHeadValue a.2.head.1.repr (BalancedRow.input (basisValues k Γ C ν) (asAtom a.2)) ≤
      value (k :: Γ) C E ν := by
  let head := actualHeadValue a.2.head.1.repr
    (BalancedRow.input (basisValues k Γ C ν) (asAtom a.2))
  have hm : (a.1 + 1) * head ∈ E.atoms.map (fun b =>
      (b.1 + 1) * actualHeadValue b.2.head.1.repr
        (BalancedRow.input (basisValues k Γ C ν) (asAtom b.2))) :=
    List.mem_map.mpr ⟨a, ha, rfl⟩
  have hs := sum_member hm
  have hcoef : head ≤ (a.1 + 1) * head := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right head (show 1 ≤ a.1 + 1 by omega)
  simp only [head, basisValues] at hcoef hs
  simp only [value, basisValues]
  omega

/-- Genuine lower-certificate expressions dominate their actual raw names.
Only the lower certificate will be used by the small-input theorem. -/
theorem rawSupportDomination : ∀ Γ : List Nat, ∀ C : Certificate Γ,
    genuineCertificate Γ C → ∀ E : Syntax Γ, genuineExpression Γ E →
    ∀ ν : Nat → Nat, ∀ i ∈ rawVariables Γ C E, ν i ≤ value Γ C E ν := by
  intro Γ
  induction Γ with
  | nil =>
    intro C hC E hE ν i hi
    exact BaseTermPrograms.Proof.supportDomination E ν i hi
  | cons k Γ ih =>
    intro C hC E hE ν i hi
    rcases List.mem_append.mp hi with hout | hhead
    · obtain ⟨j, hj, hv⟩ := List.mem_flatMap.mp hout
      have hn : E.outside j ≠ 0 := by
        intro hz
        simp only [if_pos hz, List.not_mem_nil] at hv
      have hm : i ∈ rawVariables Γ C.1 (C.2 j) := by
        simpa only [if_neg hn] using hv
      have hb := ih C.1 hC.1 (C.2 j) (hC.2 j) ν i hm
      have hc : 1 ≤ E.outside j := by omega
      have hp : value Γ C.1 (C.2 j) ν ≤ E.outside j * value Γ C.1 (C.2 j) ν := by
        simpa only [Nat.one_mul] using Nat.mul_le_mul_right (value Γ C.1 (C.2 j) ν) hc
      exact (hb.trans hp).trans (outside_le_value C E ν j)
    · obtain ⟨a, ha, hv⟩ := List.mem_flatMap.mp hhead
      obtain ⟨j, hj, hm⟩ := List.mem_flatMap.mp hv
      have hb := ih C.1 hC.1 (C.2 j) (hC.2 j) ν i hm
      let zero : Upper k := ⟨0, (fun _ => 0), []⟩
      have hw := rowWellFormed k Γ C E zero ν
      have ha' : ((a.1 + 1 : Int), asAtom a.2) ∈ (comparisonRow E zero).atoms :=
        List.mem_append_left _ (List.mem_map.mpr ⟨a, ha, rfl⟩)
      have hs := (BalancedRow.Proof.basisBounds (basisValues k Γ C ν)
        (comparisonRow E zero) hw _ ha').1
      have hmem : value Γ C.1 (C.2 j) ν ∈ basisValues k Γ C ν :=
        List.mem_ofFn.mpr ⟨j, rfl⟩
      have hdom : actualOrdinalNorm a.2.head.1.repr ≤
          BalancedRow.input (basisValues k Γ C ν) (asAtom a.2) := by
        change actualOrdinalNorm a.2.head.1.repr ≤
          actualOrdinalNorm a.2.head.1.repr + a.2.offset +
            ((List.ofFn (fun j => a.2.factors j + 1)).zipWith (· * ·)
              (basisValues k Γ C ν)).sum
        omega
      have he := HeterogeneousHead.Proof.inputExpansive a.2.head (hE a ha)
        (BalancedRow.input (basisValues k Γ C ν) (asAtom a.2)) hdom
      exact (((hb.trans (sum_member hmem)).trans hs).trans he.le).trans
        (head_le_value C E ν a ha)

theorem actualSmallInputBounds : Targets.ActualSmallInputBounds := by
  intro k Γ C E F ν hC hsmall
  obtain ⟨a, ha, hinput⟩ := hsmall
  have hsum : (basisValues k Γ C ν).sum < originalThreshold E F :=
    lt_of_le_of_lt (BalancedRow.Proof.basisBounds (basisValues k Γ C ν)
      (comparisonRow E F) (rowWellFormed k Γ C E F ν) a ha).1 hinput
  have hentry : ∀ j : Fin k, value Γ C.1 (C.2 j) ν < originalThreshold E F := by
    intro j
    have hm : value Γ C.1 (C.2 j) ν ∈ basisValues k Γ C ν :=
      List.mem_ofFn.mpr ⟨j, rfl⟩
    exact lt_of_le_of_lt (sum_member hm) hsum
  have hbasis : ∀ i ∈ basisSupport k Γ C, ν i < originalThreshold E F := by
    intro i hi
    obtain ⟨j, hj, hm⟩ := List.mem_flatMap.mp hi
    exact lt_of_le_of_lt (rawSupportDomination Γ C.1 hC.1 (C.2 j) (hC.2 j) ν i hm)
      (hentry j)
  refine ⟨hsum, hentry, hbasis, ?_⟩
  intro i hi
  rcases List.mem_append.mp hi with he | hf
  · exact hbasis i (rawSupportWithinBasis C E he)
  · exact hbasis i (rawSupportWithinBasis C F hf)

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedSmallBox.Proof
