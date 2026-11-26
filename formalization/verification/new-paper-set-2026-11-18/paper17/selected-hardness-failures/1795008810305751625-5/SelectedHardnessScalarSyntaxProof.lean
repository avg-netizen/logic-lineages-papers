module
public import LogicLineages.PermittedControl.SelectedHardnessPairSyntaxProof
public import LogicLineages.PermittedControl.SelectedSumValueProof

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedHardnessScalarSyntaxProof
open OrdinalComparison Source Source.AdmissibleAssignment Source.AdmissibleSum
open SelectedHardnessUnusedProof SelectedHardnessCombinatorSyntaxProof
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

 theorem values_repeat (n a : Nat) : SelectedSumValueProof.values (List.replicate n (a : Ordinal)) =
    ((n*a : Nat) : Ordinal) := by
  induction n with
  | zero => simp [SelectedSumValueProof.values]
  | succ n ih =>
    change ordinalNaturalSum (a : Ordinal) (SelectedSumValueProof.values (List.replicate n (a : Ordinal))) = _
    rw [ih,naturalSum_finite]
    congr 1
    simp [Nat.succ_mul,Nat.add_comm]

theorem repeated_value (ctrl : Nat → Nat) (p : Policy) {Γ}
    (ν : OrdinalComponent Γ → Ordinal) (n a : Nat) (t : OrdinalExpression Γ)
    (ht : ParametricSourceSuccessor.denoteWith ctrl ν t = (a : Ordinal)) :
    ParametricSourceSuccessor.denoteWith ctrl ν (repeated p .scalarRepeat n t) = ((n*a : Nat) : Ordinal) := by
  cases n with
  | zero => simp [repeated,ParametricSourceSuccessor.denoteWith]
  | succ n =>
    simp only [repeated]
    rw [SelectedSumValueProof.expand_value]
    simp only [List.ofFn_const,List.map_replicate,ht]
    exact values_repeat _ _

theorem unused_scalar (ctrl : Nat → Nat) (p : Policy) {Γ}
    (ν : OrdinalComponent Γ → Ordinal) (v : OrdinalVector Γ 1) (n : Nat)
    (hn : ParametricSourceSuccessor.denoteWith ctrl ν (v 0) = (n : Ordinal)) :
    ParametricSourceSuccessor.denoteWith ctrl ν (unusedVector p v 0) = ((5*n+4 : Nat) : Ordinal) := by
  change ordinalNaturalSum
    (ParametricSourceSuccessor.denoteWith ctrl ν (repeated p .scalarRepeat 4 (.add (v 0) .one)))
    (ParametricSourceSuccessor.denoteWith ctrl ν (v 0)) = _
  have ht : ParametricSourceSuccessor.denoteWith ctrl ν (.add (v 0) .one) = ((n+1 : Nat) : Ordinal) := by
    change ordinalNaturalSum (ParametricSourceSuccessor.denoteWith ctrl ν (v 0)) 1 = _
    rw [hn]
    simpa only [Nat.cast_one] using naturalSum_finite n 1
  rw [repeated_value ctrl p ν _ _ _ ht,hn,naturalSum_finite]
  congr 1
  omega

theorem higher_unused_scalar (ctrl : Nat → Nat) (p : Policy) {Γ}
    (ν : OrdinalComponent Γ → Ordinal) (v : OrdinalVector Γ 1) (n : Nat)
    (hn : ParametricSourceSuccessor.denoteWith ctrl ν (v 0) = (n : Ordinal)) :
    ParametricSourceSuccessor.denoteWith ctrl ν (higherUnusedVector p v 0) = ((9*n+8 : Nat) : Ordinal) := by
  have ht : ParametricSourceSuccessor.denoteWith ctrl ν (.add (v 0) .one) = ((n+1 : Nat) : Ordinal) := by
    change ordinalNaturalSum (ParametricSourceSuccessor.denoteWith ctrl ν (v 0)) 1 = _
    rw [hn]
    simpa only [Nat.cast_one] using naturalSum_finite n 1
  change ordinalNaturalSum
    (ParametricSourceSuccessor.denoteWith ctrl ν (repeated p .scalarRepeat 8 (.add (v 0) .one)))
    (ParametricSourceSuccessor.denoteWith ctrl ν (v 0)) = _
  rw [repeated_value ctrl p ν _ _ _ ht,hn,naturalSum_finite]
  congr 1
  omega

theorem box_tail_one (ctrl : Nat → Nat) (p : Policy) {Γ}
    (ν : OrdinalComponent Γ → Ordinal) (a b : OrdinalExpression Γ) (x y : Nat)
    (ha : ParametricSourceSuccessor.denoteWith ctrl ν a = (x : Ordinal))
    (hb : ParametricSourceSuccessor.denoteWith ctrl ν b = (y : Ordinal)) :
    ParametricSourceSuccessor.denoteWith ctrl ν (boxTail p 1 a b) = ((x+y+1 : Nat) : Ordinal) := by
  unfold boxTail
  simp only [show ¬(1=0) by decide,if_false,three]
  rw [SelectedSumValueProof.expand_value]
  simp [SelectedSumValueProof.values,List.ofFn_succ,ha,hb,numeral,repeated,
    ControlSensitivityCurrent.PolicyGadget.smallShapes.2.1 (p.shape .numeral 0),
    expand,ParametricSourceSuccessor.denoteWith,naturalSum_finite]

theorem combine_scalar_value (ctrl : Nat → Nat) (p : Policy) {Γ}
    (ν : OrdinalComponent Γ → Ordinal) (av bv : OrdinalVector Γ 1) (a0 b0 : Nat)
    (ha : ParametricSourceSuccessor.denoteWith ctrl ν (av 0) = (a0 : Ordinal))
    (hb : ParametricSourceSuccessor.denoteWith ctrl ν (bv 0) = (b0 : Ordinal)) :
    ParametricSourceSuccessor.denoteWith ctrl ν (combineVector p av bv 0) =
      (ParametricActualCollapse.collapseWith ctrl (ordinalNaturalSum
        (ordinalNaturalProduct Ordinal.omega0 (ParametricSourceSuccessor.denoteWith ctrl ν (combineHeadExpr av bv)))
        ((9*a0+5*b0+13 : Nat) : Ordinal)) : Ordinal) := by
  have hh : ordinalBoxPositive 1
      (@ordinalVectorAt Γ 2 (higherUnusedVector p av))
      (@ordinalVectorAt Γ 1 (unusedVector p bv)) 1 = combineHeadExpr av bv :=
    combine_head_expression p av bv
  have ht := box_tail_one ctrl p ν (higherUnusedVector p av 0) (unusedVector p bv 0)
    (9*a0+8) (5*b0+4) (higher_unused_scalar ctrl p ν av a0 ha) (unused_scalar ctrl p ν bv b0 hb)
  have hn : 9*a0+8+(5*b0+4)+1 = 9*a0+5*b0+13 := by omega
  change ParametricSourceSuccessor.denoteWith ctrl ν (.collapse
    (ordinalBoxPositive 1 (@ordinalVectorAt Γ 2 (higherUnusedVector p av))
      (@ordinalVectorAt Γ 1 (unusedVector p bv)) 1)
    (boxTail p 1 (higherUnusedVector p av 0) (unusedVector p bv 0))) = _
  rw [hh]
  simp only [ParametricSourceSuccessor.denoteWith,ht,hn]

end LogicLineages.PermittedControl.SelectedHardnessScalarSyntaxProof
