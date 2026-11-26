module
public import LogicLineages.PermittedControl.NaturalAffineGateGraphTargets

@[expose] public section
namespace LogicLineages.PermittedControl.NaturalAffineGateGraph
open OrdinalComparison.LayeredComparison.SnyatkovCompletion

private theorem oppositeSum (terms : List Input) (ν : Nat → Nat) :
    (terms.map (fun t => -t.1 * (ν t.2 : Int))).sum =
      -(terms.map (fun t => t.1 * (ν t.2 : Int))).sum := by
  induction terms with
  | nil => rfl
  | cons t rest ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [ih,neg_mul]
    omega

theorem signedGraph : SignedGraph := by
  intro output e ν
  simp only [graph,lowerRow,upperRow,signedValue,NormalForm.Formula.eval,NormalForm.Atom.eval,
    NormalForm.rowValue,List.map_cons,List.sum_cons,List.map_map,
    NormalForm.Summand.term,OrdinalComparison.LayeredComparison.SnyatkovCompletion.Term.value,one_mul]
  change (0 ≤ e.1 + ((-1 : Int) * (ν output : Int) +
      (e.2.map (fun t => t.1 * (ν t.2 : Int))).sum) ∧
    0 ≤ -e.1 + ((ν output : Int) +
      (e.2.map (fun t => -t.1 * (ν t.2 : Int))).sum)) ↔
    (ν output : Int) = e.1 + (e.2.map (fun t => t.1 * (ν t.2 : Int))).sum
  rw [oppositeSum]
  omega

private theorem signedValueUpdate (output y : Nat) (e : Expression) (ν : Nat → Nat)
    (fresh : ∀ t ∈ e.2, t.2 ≠ output) :
    signedValue e (Function.update ν output y) = signedValue e ν := by
  have same : e.2.map (fun t => t.1 * (Function.update ν output y t.2 : Int)) =
      e.2.map (fun t => t.1 * (ν t.2 : Int)) := by
    apply List.map_congr_left
    intro t member
    rw [Function.update_of_ne (fresh t member)]
  simp only [signedValue,same]

theorem actualNaturalExtension : ActualNaturalExtension := by
  intro output e ν fresh
  have exactAt (y : Nat) :
      (graph output e).eval (Function.update ν output y) ↔ (y : Int) = signedValue e ν := by
    rw [signedGraph,Function.update_self,signedValueUpdate output y e ν fresh]
  refine ⟨exactAt,?_,?_⟩
  · constructor
    · rintro ⟨y,holds,_⟩
      have result := (exactAt y).mp holds
      omega
    · intro nonnegative
      let y := (signedValue e ν).toNat
      have cast : (y : Int) = signedValue e ν := Int.toNat_of_nonneg nonnegative
      refine ⟨y,(exactAt y).mpr cast,?_⟩
      intro other holds
      have same := (exactAt other).mp holds
      omega
  · intro y name untouched
    exact Function.update_of_ne untouched y ν

end LogicLineages.PermittedControl.NaturalAffineGateGraph
