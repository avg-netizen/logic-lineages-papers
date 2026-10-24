import R1Calculator.Semantics
import Mathlib.Data.Finset.Sort

/-!
# Finite induced copies and genuine Sigma-one reflection

The language is exactly equality, order and ONE relation R. Complete finite
diagrams include negative atoms and equalities fixing all existing labels.
This proves Carlson's finite-set criterion (1999, Proposition 1.2) for the
literal existential/Boolean-matrix semantics used here, then instantiates it
for the standalone recursively constructed pure R1. No copy or elementarity
oracle is an input to the actual-R1 equivalence. This does not prove the
Cantor-normal-form endpoint characterization.

The diagram construction adapts the finite-diagram implementation from the
earlier Alexander thesis development; see REUSE.md for the precise scope.
-/

noncomputable section

namespace R1Calculator.PureR1

def Matrix.literal {n : Nat} (p : Prop) (φ : Matrix n) : Matrix n :=
  @ite (Matrix n) p (Classical.propDecidable p) φ (.neg φ)

theorem literal_realize {n : Nat} (p : Prop) (φ : Matrix n)
    (R : Ordinal.{0} → Ordinal.{0} → Prop) (v : Fin n → Ordinal.{0}) :
    (Matrix.literal p φ).realize R v ↔ (φ.realize R v ↔ p) := by
  by_cases hp : p <;> simp [Matrix.literal, hp, Matrix.realize]

def Matrix.finiteConjunction {n : Nat} (fs : List (Matrix n)) : Matrix n :=
  fs.foldr Matrix.conj (.neg .falsum)

theorem finiteConjunction_realize {n : Nat} (fs : List (Matrix n))
    (R : Ordinal.{0} → Ordinal.{0} → Prop) (v : Fin n → Ordinal.{0}) :
    (Matrix.finiteConjunction fs).realize R v ↔ ∀ φ ∈ fs, φ.realize R v := by
  induction fs with
  | nil => simp [Matrix.finiteConjunction, Matrix.realize]
  | cons φ fs ih =>
    change (φ.realize R v ∧ (Matrix.finiteConjunction fs).realize R v) ↔
      ∀ ψ ∈ φ :: fs, ψ.realize R v
    rw [ih]
    simp only [List.mem_cons, forall_eq_or_imp]

theorem finiteConjunction_ofFn_realize {n m : Nat} (fs : Fin m → Matrix n)
    (R : Ordinal.{0} → Ordinal.{0} → Prop) (v : Fin n → Ordinal.{0}) :
    (Matrix.finiteConjunction (List.ofFn fs)).realize R v ↔ ∀ i, (fs i).realize R v := by
  rw [finiteConjunction_realize]
  constructor
  · intro h i
    exact h (fs i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · intro h φ hφ
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hφ
    exact h i

def pairMatrix {n : Nat} (R : Ordinal.{0} → Ordinal.{0} → Prop)
    (x : Fin n → Ordinal.{0}) (i j : Fin n) : Matrix (n + n) :=
  .conj (Matrix.literal (x i = x j) (.equal (Fin.natAdd n i) (Fin.natAdd n j)))
    (.conj (Matrix.literal (x i ≤ x j) (.lessEqual (Fin.natAdd n i) (Fin.natAdd n j)))
      (Matrix.literal (R (x i) (x j)) (.first (Fin.natAdd n i) (Fin.natAdd n j))))

theorem pairMatrix_realize {n : Nat} (R : Ordinal.{0} → Ordinal.{0} → Prop)
    (x p w : Fin n → Ordinal.{0}) (i j : Fin n) :
    (pairMatrix R x i j).realize R (Fin.append p w) ↔
      (w i = w j ↔ x i = x j) ∧ (w i ≤ w j ↔ x i ≤ x j) ∧
      (R (w i) (w j) ↔ R (x i) (x j)) := by
  simp only [pairMatrix, Matrix.realize, literal_realize, Fin.append_right]

def fixedMatrix {n : Nat} (α : Ordinal.{0}) (x : Fin n → Ordinal.{0})
    (i : Fin n) : Matrix (n + n) :=
  if x i < α then .equal (Fin.castAdd n i) (Fin.natAdd n i)
  else .equal (Fin.natAdd n i) (Fin.natAdd n i)

theorem fixedMatrix_realize {n : Nat} (α : Ordinal.{0})
    (R : Ordinal.{0} → Ordinal.{0} → Prop) (x p w : Fin n → Ordinal.{0}) (i : Fin n) :
    (fixedMatrix α x i).realize R (Fin.append p w) ↔ (x i < α → p i = w i) := by
  by_cases hi : x i < α <;>
    simp only [fixedMatrix, hi, ↓reduceIte, Matrix.realize, Fin.append_left,
      Fin.append_right, true_implies, false_implies]

def diagram {n : Nat} (α : Ordinal.{0}) (R : Ordinal.{0} → Ordinal.{0} → Prop)
    (x : Fin n → Ordinal.{0}) : Matrix (n + n) :=
  Matrix.finiteConjunction (List.ofFn (fun i : Fin n =>
    Matrix.conj (fixedMatrix α x i)
      (Matrix.finiteConjunction (List.ofFn (fun j : Fin n => pairMatrix R x i j)))))

theorem diagram_realize {n : Nat} (α : Ordinal.{0})
    (R : Ordinal.{0} → Ordinal.{0} → Prop) (x p w : Fin n → Ordinal.{0}) :
    (diagram α R x).realize R (Fin.append p w) ↔
      ∀ i, (x i < α → p i = w i) ∧ ∀ j,
        (w i = w j ↔ x i = x j) ∧ (w i ≤ w j ↔ x i ≤ x j) ∧
        (R (w i) (w j) ↔ R (x i) (x j)) := by
  simp only [diagram, finiteConjunction_ofFn_realize, Matrix.realize,
    fixedMatrix_realize, pairMatrix_realize]

def diagramParameters {n : Nat} (α : Ordinal.{0})
    (x : Fin n → Ordinal.{0}) : Fin n → Ordinal.{0} :=
  fun i => if x i < α then x i else 0

theorem diagramParameters_below {n : Nat} (α : Ordinal.{0}) (hα : 0 < α)
    (x : Fin n → Ordinal.{0}) : TupleBelow α (diagramParameters α x) := by
  intro i
  by_cases hi : x i < α
  · simpa only [diagramParameters, hi, ↓reduceIte] using hi
  · simpa only [diagramParameters, hi, ↓reduceIte] using hα

theorem diagram_original {n : Nat} (α : Ordinal.{0})
    (R : Ordinal.{0} → Ordinal.{0} → Prop) (x : Fin n → Ordinal.{0}) :
    (diagram α R x).realize R (Fin.append (diagramParameters α x) x) := by
  rw [diagram_realize]
  intro i
  refine ⟨?_, fun _ => ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩⟩
  intro hi
  simp only [diagramParameters, hi, ↓reduceIte]

theorem sigma1_nonzero_lower (R : Ordinal.{0} → Ordinal.{0} → Prop)
    (α β : Ordinal.{0}) (h : Sigma1Elementary R α β) (hβ : 0 < β) : 0 < α := by
  let φ : Matrix (0 + 1) := .equal 0 0
  have hb : sigma1Truth R β 0 1 φ Fin.elim0 :=
    ⟨fun _ => 0, fun _ => hβ, rfl⟩
  obtain ⟨w, hw, _⟩ := (h 0 1 φ Fin.elim0 (fun i => Fin.elim0 i)).mpr hb
  exact (bot_le : (0 : Ordinal.{0}) ≤ w 0).trans_lt (hw 0)

/-- Reflection constructs a complete induced tuple copy, fixing every old
entry, including duplicates. Negative atomic facts are retained. -/
theorem tuple_reflection_of_lt {n : Nat} (R : Ordinal.{0} → Ordinal.{0} → Prop)
    (α β : Ordinal.{0}) (hαβ : α < β) (h : Sigma1Elementary R α β)
    (x : Fin n → Ordinal.{0}) (hx : TupleBelow β x) :
    ∃ w : Fin n → Ordinal.{0}, TupleBelow α w ∧
      (∀ i, x i < α → w i = x i) ∧
      (∀ i j, w i = w j ↔ x i = x j) ∧
      (∀ i j, w i ≤ w j ↔ x i ≤ x j) ∧
      (∀ i j, R (w i) (w j) ↔ R (x i) (x j)) := by
  have hα := sigma1_nonzero_lower R α β h ((bot_le : (0 : Ordinal.{0}) ≤ α).trans_lt hαβ)
  have hp := diagramParameters_below α hα x
  have hu : sigma1Truth R β n n (diagram α R x) (diagramParameters α x) :=
    ⟨x, hx, diagram_original α R x⟩
  obtain ⟨w, hw, hd⟩ := (h n n (diagram α R x) (diagramParameters α x) hp).mpr hu
  have he := (diagram_realize α R x (diagramParameters α x) w).mp hd
  refine ⟨w, hw, ?_, (fun i j => ((he i).2 j).1),
    (fun i j => ((he i).2 j).2.1), (fun i j => ((he i).2 j).2.2)⟩
  intro i hi
  have hv := ((he i).1 hi).symm
  simpa only [diagramParameters, hi, ↓reduceIte] using hv

/-- Full induced finite-map predicate, not a positive covering. -/
def PreservesPattern (R : Ordinal.{0} → Ordinal.{0} → Prop)
    (F : Finset Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) : Prop :=
  (∀ x ∈ F, ∀ y ∈ F, f x = f y ↔ x = y) ∧
  (∀ x ∈ F, ∀ y ∈ F, f x < f y ↔ x < y) ∧
  (∀ x ∈ F, ∀ y ∈ F, R (f x) (f y) ↔ R x y)

/-- Every finite upper set has an induced copy below alpha, with all lower
labels fixed pointwise. The function outside F is immaterial. -/
def FiniteReflection (R : Ordinal.{0} → Ordinal.{0} → Prop)
    (α β : Ordinal.{0}) : Prop :=
  ∀ F : Finset Ordinal.{0}, (∀ x ∈ F, x < β) →
    ∃ f : Ordinal.{0} → Ordinal.{0}, (∀ x ∈ F, f x < α) ∧
      (∀ x ∈ F, x < α → f x = x) ∧ PreservesPattern R F f

theorem sigma1Elementary_finiteReflection (R : Ordinal.{0} → Ordinal.{0} → Prop)
    (α β : Ordinal.{0}) (hαβ : α ≤ β) (h : Sigma1Elementary R α β) :
    FiniteReflection R α β := by
  intro F below
  by_cases hab : α = β
  · subst β
    refine ⟨id, below, (fun _ _ _ => rfl), ?_⟩
    exact ⟨fun _ _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl⟩
  · have hlt : α < β := lt_of_le_of_ne hαβ hab
    let e : F ≃ Fin F.card := F.equivFin
    let x : Fin F.card → Ordinal.{0} := fun i => (e.symm i).val
    have xmem (i : Fin F.card) : x i ∈ F := (e.symm i).property
    have xindex (μ : Ordinal.{0}) (hμ : μ ∈ F) : x (e ⟨μ, hμ⟩) = μ :=
      congrArg Subtype.val (e.symm_apply_apply ⟨μ, hμ⟩)
    obtain ⟨w, hw, fixed, heq, hle, hrel⟩ :=
      tuple_reflection_of_lt R α β hlt h x (fun i => below (x i) (xmem i))
    have hstrict (i j : Fin F.card) : w i < w j ↔ x i < x j := by
      rw [lt_iff_le_not_ge, lt_iff_le_not_ge, hle i j, hle j i]
    let f : Ordinal.{0} → Ordinal.{0} := fun μ => if hμ : μ ∈ F then w (e ⟨μ, hμ⟩) else μ
    have fmem (μ : Ordinal.{0}) (hμ : μ ∈ F) : f μ = w (e ⟨μ, hμ⟩) := by
      simp only [f, dif_pos hμ]
    refine ⟨f, ?_, ?_, ?_⟩
    · intro μ hμ
      rw [fmem μ hμ]
      exact hw _
    · intro μ hμ hμα
      rw [fmem μ hμ]
      exact (fixed _ (by simpa only [xindex μ hμ] using hμα)).trans (xindex μ hμ)
    · refine ⟨?_, ?_, ?_⟩
      · intro μ hμ ν hν
        simpa only [fmem μ hμ, fmem ν hν, xindex μ hμ, xindex ν hν] using
          heq (e ⟨μ, hμ⟩) (e ⟨ν, hν⟩)
      · intro μ hμ ν hν
        simpa only [fmem μ hμ, fmem ν hν, xindex μ hμ, xindex ν hν] using
          hstrict (e ⟨μ, hμ⟩) (e ⟨ν, hν⟩)
      · intro μ hμ ν hν
        simpa only [fmem μ hμ, fmem ν hν, xindex μ hμ, xindex ν hν] using
          hrel (e ⟨μ, hμ⟩) (e ⟨ν, hν⟩)

/-- Structural induction transports every Boolean matrix along a full
partial isomorphism. Positive preservation alone cannot transport negation. -/
theorem matrix_realize_pattern {n : Nat} (R : Ordinal.{0} → Ordinal.{0} → Prop)
    (φ : Matrix n) (F : Finset Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0})
    (pattern : PreservesPattern R F f) (v : Fin n → Ordinal.{0}) (hv : ∀ i, v i ∈ F) :
    φ.realize R (fun i => f (v i)) ↔ φ.realize R v := by
  induction φ with
  | falsum => rfl
  | equal i j => exact pattern.1 _ (hv i) _ (hv j)
  | lessEqual i j =>
    change f (v i) ≤ f (v j) ↔ v i ≤ v j
    simpa only [not_lt] using not_congr (pattern.2.1 _ (hv j) _ (hv i))
  | first i j => exact pattern.2.2 _ (hv i) _ (hv j)
  | neg φ ih => exact not_congr ih
  | conj φ ψ ihφ ihψ => exact and_congr ihφ ihψ
  | disj φ ψ ihφ ihψ => exact or_congr ihφ ihψ

theorem finiteReflection_sigma1Elementary (R : Ordinal.{0} → Ordinal.{0} → Prop)
    (α β : Ordinal.{0}) (hαβ : α ≤ β) (reflection : FiniteReflection R α β) :
    Sigma1Elementary R α β := by
  intro p m φ v hv
  constructor
  · rintro ⟨w, hw, hφ⟩
    exact ⟨w, tupleBelow_mono hαβ hw, hφ⟩
  · rintro ⟨w, hw, hφ⟩
    let F : Finset Ordinal.{0} := (List.ofFn v).toFinset ∪ (List.ofFn w).toFinset
    have vmem (i : Fin p) : v i ∈ F := Finset.mem_union.mpr
      (Or.inl (List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨i, rfl⟩)))
    have wmem (i : Fin m) : w i ∈ F := Finset.mem_union.mpr
      (Or.inr (List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨i, rfl⟩)))
    have belowF : ∀ ξ ∈ F, ξ < β := by
      intro ξ hξ
      rcases Finset.mem_union.mp hξ with hξ | hξ
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hξ)
        exact (hv i).trans_le hαβ
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hξ)
        exact hw i
    obtain ⟨f, lower, fixed, pattern⟩ := reflection F belowF
    let w' : Fin m → Ordinal.{0} := fun i => f (w i)
    have hmem : ∀ i, Fin.append v w i ∈ F := by
      apply (Fin.forall_fin_add (fun i => Fin.append v w i ∈ F)).mpr
      constructor
      · intro i
        simpa only [Fin.append_left] using vmem i
      · intro i
        simpa only [Fin.append_right] using wmem i
    have he : (fun i => f (Fin.append v w i)) = Fin.append v w' := by
      apply funext
      apply (Fin.forall_fin_add
        (fun i => f (Fin.append v w i) = Fin.append v w' i)).mpr
      constructor
      · intro i
        simpa only [Fin.append_left] using fixed (v i) (vmem i) (hv i)
      · intro i
        simp only [Fin.append_right, w']
    refine ⟨w', fun i => lower (w i) (wmem i), ?_⟩
    simpa only [he] using (matrix_realize_pattern R φ F f pattern (Fin.append v w) hmem).mpr hφ

/-- Carlson's finite criterion in the literal single-relation language. -/
theorem sigma1Elementary_iff_finiteReflection (R : Ordinal.{0} → Ordinal.{0} → Prop)
    (α β : Ordinal.{0}) (hαβ : α ≤ β) :
    Sigma1Elementary R α β ↔ FiniteReflection R α β :=
  ⟨sigma1Elementary_finiteReflection R α β hαβ,
    finiteReflection_sigma1Elementary R α β hαβ⟩

/-- The criterion concerns the ACTUAL recursively constructed pure R1.
No supplied semantic correctness assumption or reflection function occurs. -/
theorem R1_iff_finiteReflection (α β : Ordinal.{0}) :
    R1 α β ↔ α ≤ β ∧ FiniteReflection R1 α β := by
  rw [R1_iff_global]
  constructor
  · rintro ⟨h, hs⟩
    exact ⟨h, (sigma1Elementary_iff_finiteReflection R1 α β h).mp hs⟩
  · rintro ⟨h, hf⟩
    exact ⟨h, (sigma1Elementary_iff_finiteReflection R1 α β h).mpr hf⟩

theorem finiteReflection_of_R1 {α β : Ordinal.{0}} (h : R1 α β) :
    FiniteReflection R1 α β := ((R1_iff_finiteReflection α β).mp h).2

#print axioms tuple_reflection_of_lt
#print axioms matrix_realize_pattern
#print axioms sigma1Elementary_iff_finiteReflection
#print axioms R1_iff_finiteReflection

end R1Calculator.PureR1
