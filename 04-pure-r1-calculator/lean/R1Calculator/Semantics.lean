import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Common

/-!
# Standalone pure R1 semantics
The signature is exactly (=, <=, R1). Sigma-one matrices contain arbitrary
Boolean combinations and any finite block of ordinary existential quantifiers.
Empty structures and empty tuples are allowed. R1 is CONSTRUCTED by recursion
on its upper ordinal, without a supplied relation or correctness premise.
`R1_iff_global` proves the global Sigma-one equation. No simultaneous R2
relation is used. Endpoint characterization is a separate theorem.
-/
noncomputable section
namespace R1Calculator.PureR1

inductive Matrix (n : Nat) where
  | falsum
  | equal (i j : Fin n)
  | lessEqual (i j : Fin n)
  | first (i j : Fin n)
  | neg (φ : Matrix n)
  | conj (φ ψ : Matrix n)
  | disj (φ ψ : Matrix n)

def Matrix.realize {n : Nat} (R : Ordinal.{0} → Ordinal.{0} → Prop)
    (v : Fin n → Ordinal.{0}) : Matrix n → Prop
  | .falsum => False
  | .equal i j => v i = v j
  | .lessEqual i j => v i ≤ v j
  | .first i j => R (v i) (v j)
  | .neg φ => ¬ φ.realize R v
  | .conj φ ψ => φ.realize R v ∧ ψ.realize R v
  | .disj φ ψ => φ.realize R v ∨ ψ.realize R v

def TupleBelow {n : Nat} (α : Ordinal.{0}) (v : Fin n → Ordinal.{0}) : Prop :=
  ∀ i, v i < α

def sigma1Truth (R : Ordinal.{0} → Ordinal.{0} → Prop) (α : Ordinal.{0})
    (p m : Nat) (φ : Matrix (p + m)) (v : Fin p → Ordinal.{0}) : Prop :=
  ∃ w : Fin m → Ordinal.{0}, TupleBelow α w ∧ φ.realize R (Fin.append v w)

def Sigma1Elementary (R : Ordinal.{0} → Ordinal.{0} → Prop)
    (α β : Ordinal.{0}) : Prop :=
  ∀ (p m : Nat) (φ : Matrix (p + m)) (v : Fin p → Ordinal.{0}),
    TupleBelow α v → (sigma1Truth R α p m φ v ↔ sigma1Truth R β p m φ v)

theorem tupleBelow_mono {n : Nat} {α β : Ordinal.{0}}
    {v : Fin n → Ordinal.{0}} (h : α ≤ β) (hv : TupleBelow α v) : TupleBelow β v :=
  fun i => lt_of_lt_of_le (hv i) h

theorem tupleBelow_append {p m : Nat} {α : Ordinal.{0}}
    {v : Fin p → Ordinal.{0}} {w : Fin m → Ordinal.{0}}
    (hv : TupleBelow α v) (hw : TupleBelow α w) : TupleBelow α (Fin.append v w) := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa only [Fin.append_left] using hv j
  · intro j
    simpa only [Fin.append_right] using hw j

theorem Matrix.realize_congr {n : Nat}
    {R S : Ordinal.{0} → Ordinal.{0} → Prop} {v : Fin n → Ordinal.{0}}
    (h : ∀ i j, R (v i) (v j) ↔ S (v i) (v j)) (φ : Matrix n) :
    φ.realize R v ↔ φ.realize S v := by
  induction φ with
  | falsum => rfl
  | equal => rfl
  | lessEqual => rfl
  | first i j => exact h i j
  | neg φ ih => exact not_congr ih
  | conj φ ψ ihφ ihψ => exact and_congr ihφ ihψ
  | disj φ ψ ihφ ihψ => exact or_congr ihφ ihψ

theorem sigma1Elementary_refl (R : Ordinal.{0} → Ordinal.{0} → Prop)
    (α : Ordinal.{0}) : Sigma1Elementary R α α := fun _ _ _ _ _ => Iff.rfl

abbrev Level := Ordinal.{0} → Prop

def previousRelation (β : Ordinal.{0})
    (previous : ∀ γ : Ordinal.{0}, γ < β → Level) (x y : Ordinal.{0}) : Prop :=
  if hy : y < β then previous y hy x else False

/-- Only strictly smaller upper ordinals occur in the recursive step. -/
def step (β : Ordinal.{0})
    (previous : ∀ γ : Ordinal.{0}, γ < β → Level) : Level :=
  fun α => α ≤ β ∧ Sigma1Elementary (previousRelation β previous) α β

def family (β : Ordinal.{0}) : Level := Ordinal.lt_wf.fix step β

/-- Actual standalone pure R1, constructed rather than postulated. -/
def R1 (α β : Ordinal.{0}) : Prop := family β α

def prefixRelation (β x y : Ordinal.{0}) : Prop := y < β ∧ R1 x y

theorem previousRelation_family (β : Ordinal.{0}) :
    previousRelation β (fun γ _ => family γ) = prefixRelation β := by
  funext x y
  apply propext
  by_cases h : y < β <;> simp only [previousRelation, prefixRelation, R1, h, ↓reduceDIte,
    true_and, false_and]

theorem family_eq (β : Ordinal.{0}) : family β = step β (fun γ _ => family γ) :=
  WellFounded.fix_eq Ordinal.lt_wf step β

/-- Literal well-founded-recursion equation. -/
theorem R1_iff (α β : Ordinal.{0}) :
    R1 α β ↔ α ≤ β ∧ Sigma1Elementary (prefixRelation β) α β := by
  unfold R1
  rw [family_eq, step, previousRelation_family]

theorem prefix_below {β x y : Ordinal.{0}} (hy : y < β) :
    prefixRelation β x y ↔ R1 x y := and_iff_right hy

theorem Matrix.realize_prefix {n : Nat} {β : Ordinal.{0}}
    {v : Fin n → Ordinal.{0}} (hv : TupleBelow β v) (φ : Matrix n) :
    φ.realize (prefixRelation β) v ↔ φ.realize R1 v :=
  φ.realize_congr (fun _ j => prefix_below (hv j))

theorem sigma1Truth_prefix {α β : Ordinal.{0}} (hαβ : α ≤ β)
    (p m : Nat) (φ : Matrix (p + m)) (v : Fin p → Ordinal.{0})
    (hv : TupleBelow α v) :
    sigma1Truth (prefixRelation β) α p m φ v ↔ sigma1Truth R1 α p m φ v := by
  constructor
  · rintro ⟨w, hw, hφ⟩
    exact ⟨w, hw, (φ.realize_prefix (tupleBelow_mono hαβ (tupleBelow_append hv hw))).mp hφ⟩
  · rintro ⟨w, hw, hφ⟩
    exact ⟨w, hw, (φ.realize_prefix (tupleBelow_mono hαβ (tupleBelow_append hv hw))).mpr hφ⟩

theorem sigma1Elementary_prefix {α β : Ordinal.{0}} (hαβ : α ≤ β) :
    Sigma1Elementary (prefixRelation β) α β ↔ Sigma1Elementary R1 α β := by
  constructor
  · intro h p m φ v hv
    exact (sigma1Truth_prefix hαβ p m φ v hv).symm.trans
      ((h p m φ v hv).trans
        (sigma1Truth_prefix le_rfl p m φ v (tupleBelow_mono hαβ hv)))
  · intro h p m φ v hv
    exact (sigma1Truth_prefix hαβ p m φ v hv).trans
      ((h p m φ v hv).trans
        (sigma1Truth_prefix le_rfl p m φ v (tupleBelow_mono hαβ hv)).symm)

/-- GLOBAL Sigma-one initial-segment equation, proved from the recursion. -/
theorem R1_iff_global (α β : Ordinal.{0}) :
    R1 α β ↔ α ≤ β ∧ Sigma1Elementary R1 α β := by
  rw [R1_iff]
  constructor
  · rintro ⟨h, hs⟩
    exact ⟨h, (sigma1Elementary_prefix h).mp hs⟩
  · rintro ⟨h, hs⟩
    exact ⟨h, (sigma1Elementary_prefix h).mpr hs⟩

/-- Truth depends only on relations between elements below the ambient bound. -/
theorem sigma1Truth_congr_below
    {R S : Ordinal.{0} → Ordinal.{0} → Prop} {α β : Ordinal.{0}}
    (hαβ : α ≤ β) (hRS : ∀ x y, y < β → (R x y ↔ S x y))
    (p m : Nat) (φ : Matrix (p + m)) (v : Fin p → Ordinal.{0})
    (hv : TupleBelow α v) : sigma1Truth R α p m φ v ↔ sigma1Truth S α p m φ v := by
  constructor
  · rintro ⟨w, hw, hφ⟩
    have ht := tupleBelow_mono hαβ (tupleBelow_append hv hw)
    exact ⟨w, hw, (φ.realize_congr (fun i j => hRS _ _ (ht j))).mp hφ⟩
  · rintro ⟨w, hw, hφ⟩
    have ht := tupleBelow_mono hαβ (tupleBelow_append hv hw)
    exact ⟨w, hw, (φ.realize_congr (fun i j => hRS _ _ (ht j))).mpr hφ⟩

theorem sigma1Elementary_congr_below
    {R S : Ordinal.{0} → Ordinal.{0} → Prop} {α β : Ordinal.{0}}
    (hαβ : α ≤ β) (hRS : ∀ x y, y < β → (R x y ↔ S x y)) :
    Sigma1Elementary R α β ↔ Sigma1Elementary S α β := by
  constructor
  · intro h p m φ v hv
    exact (sigma1Truth_congr_below hαβ hRS p m φ v hv).symm.trans
      ((h p m φ v hv).trans
        (sigma1Truth_congr_below le_rfl hRS p m φ v (tupleBelow_mono hαβ hv)))
  · intro h p m φ v hv
    exact (sigma1Truth_congr_below hαβ hRS p m φ v hv).trans
      ((h p m φ v hv).trans
        (sigma1Truth_congr_below le_rfl hRS p m φ v (tupleBelow_mono hαβ hv)).symm)

/-- Uniqueness is a theorem about candidate relations, not an assumed
correctness property of the constructed relation. Its proof is upper-ordinal
induction using full Boolean-matrix truth locality. -/
theorem R1_unique (R : Ordinal.{0} → Ordinal.{0} → Prop)
    (hR : ∀ α β, R α β ↔ α ≤ β ∧ Sigma1Elementary R α β) : R = R1 := by
  have h : ∀ β, ∀ α, R α β ↔ R1 α β := by
    intro β
    induction β using Ordinal.lt_wf.induction with
    | h β ih =>
      intro α
      rw [hR, R1_iff_global]
      by_cases hαβ : α ≤ β
      · exact and_congr Iff.rfl
          (sigma1Elementary_congr_below hαβ (fun x y hy => ih y hy x))
      · simp only [hαβ, false_and]
  funext α β
  exact propext (h β α)

/-- Local uniqueness needs the semantic equation only BELOW the given
ordinal horizon. No global characterization outside it is assumed. -/
theorem R1_unique_below (Ω : Ordinal.{0}) (R : Ordinal.{0} → Ordinal.{0} → Prop)
    (hR : ∀ α β, β < Ω → (R α β ↔ α ≤ β ∧ Sigma1Elementary R α β)) :
    ∀ α β, β < Ω → (R α β ↔ R1 α β) := by
  have h : ∀ β, β < Ω → ∀ α, R α β ↔ R1 α β := by
    intro β
    induction β using Ordinal.lt_wf.induction with
    | h β ih =>
      intro hβ α
      rw [hR α β hβ, R1_iff_global]
      by_cases hαβ : α ≤ β
      · exact and_congr Iff.rfl
          (sigma1Elementary_congr_below hαβ
            (fun x y hy => ih y hy (lt_trans hy hβ) x))
      · simp only [hαβ, false_and]
  exact fun α β hβ => h β hβ α

#print axioms R1_unique_below

#print axioms R1_unique

#print axioms R1_iff_global
end R1Calculator.PureR1
