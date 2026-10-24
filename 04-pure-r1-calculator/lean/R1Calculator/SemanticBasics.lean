import R1Calculator.Semantics
import Mathlib.Data.Finset.Lattice.Fold

/-! Basic laws of the actual standalone pure R1, derived from its constructed
Sigma-one semantics. No endpoint characterization is an assumption. -/
noncomputable section
namespace R1Calculator.PureR1

theorem sigma1Truth_mono {R : Ordinal.{0} → Ordinal.{0} → Prop}
    {α β : Ordinal.{0}} (hαβ : α ≤ β)
    {p m : Nat} {φ : Matrix (p + m)} {v : Fin p → Ordinal.{0}} :
    sigma1Truth R α p m φ v → sigma1Truth R β p m φ v := by
  rintro ⟨w, hw, hφ⟩
  exact ⟨w, tupleBelow_mono hαβ hw, hφ⟩

theorem sigma1Elementary_trans {R : Ordinal.{0} → Ordinal.{0} → Prop}
    {α β γ : Ordinal.{0}} (hαβ : α ≤ β)
    (hab : Sigma1Elementary R α β) (hbc : Sigma1Elementary R β γ) :
    Sigma1Elementary R α γ := by
  intro p m φ v hv
  exact (hab p m φ v hv).trans (hbc p m φ v (tupleBelow_mono hαβ hv))

theorem sigma1Elementary_between {R : Ordinal.{0} → Ordinal.{0} → Prop}
    {α β γ : Ordinal.{0}} (hab : Sigma1Elementary R α β)
    (hac : α ≤ γ) (hcb : γ ≤ β) : Sigma1Elementary R α γ := by
  intro p m φ v hv
  constructor
  · exact sigma1Truth_mono hac
  · intro hγ
    exact (hab p m φ v hv).mpr (sigma1Truth_mono hcb hγ)

theorem R1_le {α β : Ordinal.{0}} (h : R1 α β) : α ≤ β :=
  ((R1_iff_global α β).mp h).1

theorem R1_elementary {α β : Ordinal.{0}} (h : R1 α β) :
    Sigma1Elementary R1 α β := ((R1_iff_global α β).mp h).2

theorem R1_refl (α : Ordinal.{0}) : R1 α α :=
  (R1_iff_global α α).mpr ⟨le_rfl, sigma1Elementary_refl R1 α⟩

theorem R1_trans {α β γ : Ordinal.{0}} (hab : R1 α β) (hbc : R1 β γ) : R1 α γ :=
  (R1_iff_global α γ).mpr ⟨le_trans (R1_le hab) (R1_le hbc),
    sigma1Elementary_trans (R1_le hab) (R1_elementary hab) (R1_elementary hbc)⟩

/-- Initial segments of an R1 interval are R1 intervals (Carlson Lemma 2.1(2)). -/
theorem R1_between {α β γ : Ordinal.{0}} (hab : R1 α β)
    (hac : α ≤ γ) (hcb : γ ≤ β) : R1 α γ :=
  (R1_iff_global α γ).mpr ⟨hac,
    sigma1Elementary_between (R1_elementary hab) hac hcb⟩

theorem R1_antisymm {α β : Ordinal.{0}} (hab : R1 α β) (hba : R1 β α) : α = β :=
  le_antisymm (R1_le hab) (R1_le hba)

/-- Predecessors of a common endpoint are linearly ordered by R1. -/
theorem R1_predecessors {α β γ : Ordinal.{0}} (hac : R1 α γ) (hbc : R1 β γ) :
    R1 α β ∨ R1 β α := by
  rcases le_total α β with hab | hba
  · exact Or.inl (R1_between hac hab (R1_le hbc))
  · exact Or.inr (R1_between hbc hba (R1_le hac))

/-- Crossing a known R1 interval is equivalent to reaching its left endpoint. -/
theorem R1_cross_cut {α β x y : Ordinal.{0}} (hab : R1 α β)
    (hx : x ≤ α) (hay : α ≤ y) (hyb : y ≤ β) :
    R1 x y ↔ R1 x α := by
  constructor
  · intro hxy
    exact R1_between hxy hx hay
  · intro hxa
    exact R1_trans hxa (R1_between hab hay hyb)

/-- Elementarity reflects nonemptiness, including the empty-domain edge case. -/
theorem R1_pos {α β : Ordinal.{0}} (h : R1 α β) (hβ : 0 < β) : 0 < α := by
  have he := R1_elementary h 0 1 (.neg .falsum) Fin.elim0
    (fun i => Fin.elim0 i)
  have ht : sigma1Truth R1 β 0 1 (.neg .falsum) Fin.elim0 :=
    ⟨fun _ => 0, fun _ => hβ, fun hfalse => hfalse⟩
  obtain ⟨w, hw, _⟩ := he.mpr ht
  exact lt_of_le_of_lt (show 0 ≤ w 0 from bot_le) (hw 0)

@[simp] theorem R1_zero_iff (β : Ordinal.{0}) : R1 0 β ↔ β = 0 := by
  constructor
  · intro h
    by_contra hβ
    exact (lt_irrefl 0) (R1_pos h (lt_of_le_of_ne (show 0 ≤ β from bot_le) (Ne.symm hβ)))
  · rintro rfl
    exact R1_refl 0

/-- Any proper R1 extension forces room above every parameter in its left
initial segment. This uses the actual one-witness formula x < witness. -/
theorem R1_no_max {α β : Ordinal.{0}} (h : R1 α β) (hαβ : α < β)
    (x : Ordinal.{0}) (hx : x < α) : ∃ y, y < α ∧ x < y := by
  let φ : Matrix (1 + 1) := .neg (.lessEqual 1 0)
  have he := R1_elementary h 1 1 φ (fun _ => x) (fun _ => hx)
  have ht : sigma1Truth R1 β 1 1 φ (fun _ => x) := by
    refine ⟨fun _ => α, fun _ => hαβ, ?_⟩
    change ¬ α ≤ x
    exact not_le.mpr hx
  obtain ⟨w, hw, hφ⟩ := he.mpr ht
  refine ⟨w 0, hw 0, ?_⟩
  change ¬ w 0 ≤ x at hφ
  exact lt_of_not_ge hφ

/-- Successor ordinals have no proper R1 extensions (Carlson Lemma 2.1(5)). -/
@[simp] theorem R1_succ_iff (α β : Ordinal.{0}) :
    R1 (Order.succ α) β ↔ β = Order.succ α := by
  constructor
  · intro h
    by_contra hne
    have hlt : Order.succ α < β := lt_of_le_of_ne (R1_le h) (Ne.symm hne)
    obtain ⟨y, hy, hαy⟩ := R1_no_max h hlt α (Order.lt_succ α)
    exact (not_lt_of_ge (Order.lt_succ_iff.mp hy)) hαy
  · rintro rfl
    exact R1_refl _

/-- A proper R1 predecessor is a nonzero limit ordinal. -/
theorem R1_isSuccLimit {α β : Ordinal.{0}} (h : R1 α β) (hαβ : α < β) :
    Order.IsSuccLimit α := by
  refine ⟨?_, Order.isSuccPrelimit_of_succ_lt ?_⟩
  · exact not_isMin_iff_bot_lt.mpr
      (R1_pos h (lt_of_le_of_lt (show 0 ≤ α from bot_le) hαβ))
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := R1_no_max h hαβ x hx
    exact lt_of_le_of_lt (Order.succ_le_iff.mpr hxy) hy

/-- R1 intervals are closed at suprema: cofinally many upper bounds suffice.
The proof bounds the entire finite existential witness tuple by one ordinal;
there is no compactness or infinitary-formula assumption. -/
theorem R1_of_cofinal {α β : Ordinal.{0}} (hαβ : α ≤ β)
    (hcof : ∀ c < β, ∃ γ, c < γ ∧ R1 α γ) : R1 α β := by
  by_cases hβ : β = 0
  · subst β
    have hα : α = 0 := le_antisymm hαβ bot_le
    subst α
    exact R1_refl 0
  apply (R1_iff_global α β).mpr
  refine ⟨hαβ, ?_⟩
  intro p m φ v hv
  constructor
  · exact sigma1Truth_mono hαβ
  · rintro ⟨w, hw, hφ⟩
    have hpos : (⊥ : Ordinal.{0}) < β := bot_lt_iff_ne_bot.mpr hβ
    have hmax : Finset.univ.sup w < β :=
      (Finset.sup_lt_iff hpos).mpr (fun i _ => hw i)
    obtain ⟨γ, hγ, hR⟩ := hcof (Finset.univ.sup w) hmax
    have hwγ : TupleBelow γ w := by
      intro i
      exact lt_of_le_of_lt (Finset.le_sup (Finset.mem_univ i)) hγ
    exact (R1_elementary hR p m φ v hv).mpr ⟨w, hwγ, hφ⟩

#print axioms R1_isSuccLimit
#print axioms R1_of_cofinal

#print axioms R1_zero_iff
#print axioms R1_succ_iff

#print axioms R1_trans
#print axioms R1_between
#print axioms R1_cross_cut
end R1Calculator.PureR1
