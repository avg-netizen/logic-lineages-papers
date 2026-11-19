module
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundConstructionTargets
public import LogicLineages.ControlSensitivityCurrent.CurrentReserveAlgebraProof
public import LogicLineages.OrdinalComparison.OriginalScaleFlatListAlgebraProof
public import LogicLineages.OrdinalComparison.OriginalScaleFlatListReplicationProof
public import LogicLineages.OrdinalComparison.WWOriginalValueClosureProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentGroundConstruction

open LogicLineages.OrdinalComparison
open LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof (finiteNorm)
open ParametricSourceSuccessor
open FunctionalDetector.Proof
open CurrentReserve (unitValue zeroUnits)

theorem exactReplication : CurrentGroundConstructionTargets.ExactReplication := by
  intro Γ b xs caller
  constructor
  · simp [paidList,OriginalScaleFlatList.Proof.flatten_replicate_length]
  · simp [OriginalScaleCompilerCode.paidCode,paidList,scale,
      List.map_append,List.map_flatten,List.map_replicate]

private theorem powerBelow {a : Ordinal} (ha : a < epsilonZero) :
    (2 : Ordinal)^a < epsilonZero := by
  have hw : Ordinal.omega0^a < epsilonZero :=
    (Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).2 ha
  exact (Ordinal.opow_le_opow_left a (Ordinal.natCast_lt_omega0 2).le).trans_lt hw

private theorem productBelow {a b : Ordinal} (ha : a < epsilonZero) (hb : b < epsilonZero) :
    ordinalNaturalProduct a b < epsilonZero := by
  obtain ⟨x,hx⟩ := normalRepresentationComplete a ha
  obtain ⟨y,hy⟩ := normalRepresentationComplete b hb
  rw [← hx,← hy,← naturalProductDenotation x y]
  exact normalRepresentationSound (naturalProduct x y)

/-- The stronger arithmetic helper works even for arbitrary expression
payloads, not just the generated ones ultimately used. Unit valuations
are finite and every collapse evaluation returns an actual natural. -/
theorem unitBelow (f : Nat → Nat) {Γ} (q : OrdinalExpression Γ) : unitValue f q < epsilonZero := by
  unfold unitValue
  rw [zeroUnits]
  induction q with
  | var x => simpa only [denoteWith,Nat.cast_one] using (finiteNorm 1).1
  | zero => exact zero_lt_epsilonZero
  | one => simpa only [denoteWith,Nat.cast_one] using (finiteNorm 1).1
  | omega =>
    have h := (Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).2
      (show (1 : Ordinal) < epsilonZero by simpa using (finiteNorm 1).1)
    simpa only [denoteWith,Ordinal.opow_one,epsilonZero] using h
  | add a b ih₁ ih₂ => exact sum_below_epsilon _ _ ih₁ ih₂
  | emul a b ih₁ ih₂ => exact productBelow (powerBelow ih₁) ih₂
  | collapse a b _ _ => exact (finiteNorm _).1

theorem exactPositiveGap : CurrentGroundConstructionTargets.ExactPositiveGap := by
  intro Γ f b c xs caller hb hc
  have hn : 2 ≤ scale b := OriginalScaleFlatList.Proof.scale_two b hb
  have hd : 1 ≤ c-3*xs.length-3 := by omega
  have hp := Nat.mul_le_mul hn hd
  change 2*1 ≤ scale b*(c-3*xs.length-3) at hp
  have hp' : 0 < gap b xs.length c ∧ gap b xs.length c + 1 = scale b * (c-3*xs.length-3) := by
    unfold gap
    omega
  refine ⟨hp'.1,hp'.2,?_⟩
  let vals := xs.map (fun op => unitValue f (op.vector 1))
  let a := unitValue f (caller.vector 1)
  have hvals : ∀ x ∈ vals, x < epsilonZero := by
    intro x hx
    obtain ⟨op,_,rfl⟩ := List.mem_map.mp hx
    exact unitBelow f (op.vector 1)
  have ha : a < epsilonZero := unitBelow f (caller.vector 1)
  have hc' : 3*vals.length+4 ≤ c := by simpa [vals] using hc
  have h := OriginalScaleFlatList.Proof.flat_balance vals a (scale b) c hvals ha hn hc'
  have hz : ((paidList b xs caller).map (fun x => unitValue f (x.vector 1))) =
      (List.replicate (scale b) vals).flatten ++ List.replicate (scale b) a := by
    simp only [paidList,List.map_append,List.map_replicate,vals,a]
    exact congrArg (fun ys : List Ordinal => ys ++ List.replicate (scale b) (unitValue f (caller.vector 1)))
      (OriginalScaleFlatList.Proof.map_flatten_replicate
        (fun op : Operator Γ => unitValue f (op.vector 1)) (scale b) xs)
  simpa only [chargedSum,hz, gap,vals,List.length_map,a] using h

end LogicLineages.ControlSensitivityCurrent.CurrentGroundConstruction
