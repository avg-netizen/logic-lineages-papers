module
public import LogicLineages.OrdinalComparison.OriginalScaleFlatListTargets
public import LogicLineages.OrdinalComparison.HeterogeneousUnaryAssemblyProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalScaleFlatList.Proof
open HeterogeneousUnaryAssembly ScalarCarrierAccounting OriginalDomain

theorem flatten_replicate_length {α : Type} (n : Nat) (xs : List α) :
    (List.replicate n xs).flatten.length = n*xs.length := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ,List.flatten_cons,ih,Nat.succ_mul,Nat.add_comm]

theorem map_flatten_replicate {α β : Type} (f : α → β) (n : Nat) (xs : List α) :
    ((List.replicate n xs).flatten).map f = (List.replicate n (xs.map f)).flatten := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,List.flatten_cons,List.map_append,ih]

theorem literalReplication : Targets.LiteralReplication := by
  intro Γ b xs caller
  constructor
  · simp [paidList,flatten_replicate_length]
  · simp [paidList,List.map_append,map_flatten_replicate]

theorem scale_two (b : Nat) (hb : 4 ≤ b) : 2 ≤ scale b := by
  cases b with
  | zero => omega
  | succ b =>
    have hp : 0 < 2^b := Nat.pow_pos (by decide)
    simp only [scale,pow_succ]
    omega

theorem exactPositiveGap : Targets.ExactPositiveGap := by
  intro Γ b xs c hb hc
  have hn := scale_two b hb
  have hd : 1 ≤ c-3*xs.length-3 := by omega
  have hp := Nat.mul_le_mul hn hd
  change 2*1 ≤ scale b*(c-3*xs.length-3) at hp
  unfold gap
  omega

theorem actual_head_below {Γ : List Ty} {τ : Ty}
    (t : OriginalTerm Γ τ) (u : OrdinalVector Γ τ.level)
    (hu : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t = some u)
    (j : Fin (τ.level+1)) (hj : 0 < j.val) : unitValue (u j) < epsilonZero := by
  obtain ⟨u',hu',hg⟩ := AdmissibleAssignment.actualAdmissibleAssignmentGenerated Γ τ OrdinalSyntax.defaultPolicy t
  have he : u' = u := Option.some.inj (hu'.symm.trans hu)
  subst u'
  have hp := originalExpressionValueBelowEpsilonZero Γ (UnitObservation.substitution (fun _ => 0)) (u j)
  rw [UnaryCarrier.Proof.positive_unit_value j.val (u j) hj (hg j) (fun _ => 0)] at hp
  exact hp

theorem record_head_below {Γ : List Ty} (op : Operator Γ) : unitValue (op.vector 1) < epsilonZero :=
  actual_head_below op.term op.vector op.assigned 1 (by decide)
end LogicLineages.OrdinalComparison.Source.OriginalScaleFlatList.Proof
