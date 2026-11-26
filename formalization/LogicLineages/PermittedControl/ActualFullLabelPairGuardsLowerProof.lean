module
public import LogicLineages.PermittedControl.ActualFullLabelPairGuardsTargets
import LogicLineages.PermittedControl.OriginalMatrixLinearRowFormulaShapeProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualFullLabelPairGuards
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open ActualFullValueLabels (Label ActualLabel)
open PreparedProjection
open OriginalMatrixLinearRowFormula (safeAtom safeAnd)

private theorem signAnswer (u v : Nat) :
    (numericalComparison u v = 0 ↔ u < v) ∧
    (numericalComparison u v = 1 ↔ u = v) ∧ (numericalComparison u v = 2 ↔ v < u) := by
  rcases lt_trichotomy u v with less | eq | greater
  · have ne := ne_of_lt less
    have ng := not_lt_of_ge less.le
    simp [numericalComparison,less,ne,ng]
  · subst v
    simp [numericalComparison]
  · have ne : u ≠ v := (ne_of_lt greater).symm
    have nl := not_lt_of_ge greater.le
    simp [numericalComparison,nl,ne,greater]

private theorem twoAtoms (ops : List LowerOperand) (b : Int) (w₁ w₂ : Int) (i j : Nat)
    (hi : i ≤ ops.length) (hj : j ≤ ops.length) :
    PreparedInput ops (.atom (.nonnegative (b,[(w₁,.variable i),(w₂,.variable j)]))) := by
  apply safeAtom
  · intro term used
    rcases List.mem_cons.mp used with head | rest
    · subst term
      exact ⟨i,rfl⟩
    · have tail := List.mem_singleton.mp rest
      subst term
      exact ⟨j,rfl⟩
  · intro n used
    change n ∈ [i,j] at used
    rcases List.mem_cons.mp used with head | rest
    · simpa only [head] using hi
    · have tail := List.mem_singleton.mp rest
      simpa only [tail] using hj

theorem lowerShape (p : Pair) (a : Answer) :
    PreparedInput (lowerPacket p a).1 (lowerPacket p a).2 := by
  let ops := (lowerPacket p a).1
  have one : 1 ≤ ops.length := by change 1 ≤ 2; decide
  have two : 2 ≤ ops.length := by change 2 ≤ 2; decide
  cases a with
  | less => exact twoAtoms ops (-1) 1 (-1) 2 1 two one
  | equal =>
      exact safeAnd ops _ _ (twoAtoms ops 0 1 (-1) 1 2 one two)
        (twoAtoms ops 0 1 (-1) 2 1 two one)
  | greater => exact twoAtoms ops (-1) 1 (-1) 1 2 one two

theorem lowerMeaning (a : Answer) (ν : Nat → Nat) :
    (lowerFormula a).eval ν ↔ numericalComparison (ν 1) (ν 2) = a.code := by
  obtain ⟨less,equal,greater⟩ := signAnswer (ν 1) (ν 2)
  cases a with
  | less =>
      change (0 ≤ (-1 : Int) + (1 * (ν 2 : Int) + ((-1) * (ν 1 : Int) + 0))) ↔ _
      rw [Answer.code,less]
      simp only [one_mul,neg_one_mul,add_zero]
      omega
  | equal =>
      change ((0 ≤ (0 : Int) + (1 * (ν 1 : Int) + ((-1) * (ν 2 : Int) + 0))) ∧
        0 ≤ (0 : Int) + (1 * (ν 2 : Int) + ((-1) * (ν 1 : Int) + 0))) ↔ _
      rw [Answer.code,equal]
      simp only [one_mul,neg_one_mul,add_zero,zero_add]
      omega
  | greater =>
      change (0 ≤ (-1 : Int) + (1 * (ν 1 : Int) + ((-1) * (ν 2 : Int) + 0))) ↔ _
      rw [Answer.code,greater]
      simp only [one_mul,neg_one_mul,add_zero]
      omega

end LogicLineages.PermittedControl.ActualFullLabelPairGuards
