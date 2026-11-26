module
public import LogicLineages.PermittedControl.AffineCollapseGraphCompositionTargets
import LogicLineages.PermittedControl.NaturalAffineGateGraphSemanticProof
import LogicLineages.PermittedControl.FixedHeadCollapseGraphSemanticProof

@[expose] public section
namespace LogicLineages.PermittedControl.AffineCollapseGraphComposition
open OrdinalComparison

private theorem insertedInput (ν : Nat → Nat) (inputName outputName : Nat)
    (values : Nat × Nat) (different : inputName ≠ outputName) :
    insertValues ν inputName outputName values inputName = values.1 := by
  rw [insertValues,Function.update_of_ne different,Function.update_self]

private theorem insertedOutput (ν : Nat → Nat) (inputName outputName : Nat)
    (values : Nat × Nat) :
    insertValues ν inputName outputName values outputName = values.2 := by
  exact Function.update_self _ _ _

private theorem untouched (ν : Nat → Nat) (inputName outputName : Nat)
    (values : Nat × Nat) (name : Nat) (notInput : name ≠ inputName) (notOutput : name ≠ outputName) :
    insertValues ν inputName outputName values name = ν name := by
  rw [insertValues,Function.update_of_ne notOutput,Function.update_of_ne notInput]

private theorem signedValueAt (e : Expression) (ν : Nat → Nat) (inputName outputName : Nat)
    (values : Nat × Nat) (fresh : Fresh e inputName outputName) :
    NaturalAffineGateGraph.signedValue e (insertValues ν inputName outputName values) =
      NaturalAffineGateGraph.signedValue e ν := by
  have reads : e.2.map (fun t => t.1 * (insertValues ν inputName outputName values t.2 : Int)) =
      e.2.map (fun t => t.1 * (ν t.2 : Int)) := by
    apply List.map_congr_left
    intro t member
    obtain ⟨notInput,notOutput⟩ := fresh.2 t member
    rw [untouched ν inputName outputName values t.2 notInput notOutput]
  simp only [NaturalAffineGateGraph.signedValue,reads]

private theorem exactAt (f : Nat → Nat) (B : Nat) (selected : SelectedWithThreshold f B)
    (head : Nat) (e : Expression) (inputName outputName : Nat) (ν : Nat → Nat)
    (fresh : Fresh e inputName outputName) (values : Nat × Nat) :
    graph f head e inputName outputName (insertValues ν inputName outputName values) ↔
      originalDomain head e ν ∧ values = originalValues f head e ν := by
  rw [graph,NaturalAffineGateGraph.signedGraph,insertedInput ν inputName outputName values fresh.1,
    insertedOutput ν inputName outputName values,signedValueAt e ν inputName outputName values fresh]
  rw [((FixedHeadCollapseGraph.sourceGraph f B selected (head,values.1)).1 values.2)]
  let s := NaturalAffineGateGraph.signedValue e ν
  change ((values.1 : Int) = s ∧ FixedHeadCollapseGraph.domain (head,values.1) ∧
    values.2 = headCollapse f (rawNoteDecode head).repr values.1) ↔
    (0 ≤ s ∧ FixedHeadCollapseGraph.domain (head,s.toNat)) ∧
    values = (s.toNat,headCollapse f (rawNoteDecode head).repr s.toNat)
  constructor
  · rintro ⟨signed,admitted,result⟩
    have nonnegative : 0 ≤ s := by omega
    have cast : (s.toNat : Int) = s := Int.toNat_of_nonneg nonnegative
    have inputExact : values.1 = s.toNat := by omega
    refine ⟨⟨nonnegative,?_⟩,Prod.ext inputExact ?_⟩
    · rw [← inputExact]
      exact admitted
    · change values.2 = headCollapse f (rawNoteDecode head).repr s.toNat
      rw [← inputExact]
      exact result
  · rintro ⟨⟨nonnegative,admitted⟩,rfl⟩
    exact ⟨Int.toNat_of_nonneg nonnegative,admitted,rfl⟩

theorem exactPairExtension : ExactPairExtension := by
  intro f B selected head e inputName outputName ν fresh
  have correct := exactAt f B selected head e inputName outputName ν fresh
  refine ⟨correct,?_,untouched ν inputName outputName⟩
  constructor
  · rintro ⟨values,holds,_⟩
    exact ((correct values).mp holds).1
  · intro domain
    refine ⟨originalValues f head e ν, (correct _).mpr ⟨domain,rfl⟩,?_⟩
    intro other holds
    exact ((correct other).mp holds).2

end LogicLineages.PermittedControl.AffineCollapseGraphComposition
