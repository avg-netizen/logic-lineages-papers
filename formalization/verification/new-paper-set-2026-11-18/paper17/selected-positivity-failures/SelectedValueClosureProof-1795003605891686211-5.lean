module
public import LogicLineages.PermittedControl.SelectedPositivityTargets
public import LogicLineages.PermittedControl.SourceScalarCalibrationProof
public import LogicLineages.OrdinalComparison.NaturalProductInterpretation
public import LogicLineages.OrdinalComparison.OrdinalRepresentationComplete

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedValueClosureProof
open OrdinalComparison Source SelectedSourceDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

theorem sum_below {a b : Ordinal} (ha : a < epsilonZero) (hb : b < epsilonZero) :
    ordinalNaturalSum a b < epsilonZero := by
  obtain ⟨x, hx⟩ := normalRepresentationComplete a ha
  obtain ⟨y, hy⟩ := normalRepresentationComplete b hb
  rw [← hx, ← hy, ← naturalSumDenotation x y]
  exact normalRepresentationSound (naturalSum x y)

theorem product_below {a b : Ordinal} (ha : a < epsilonZero) (hb : b < epsilonZero) :
    ordinalNaturalProduct a b < epsilonZero := by
  obtain ⟨x, hx⟩ := normalRepresentationComplete a ha
  obtain ⟨y, hy⟩ := normalRepresentationComplete b hb
  rw [← hx, ← hy, ← naturalProductDenotation x y]
  exact normalRepresentationSound (naturalProduct x y)

theorem omega_below : Ordinal.omega0 < epsilonZero := by
  have h := (Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr
    (show (1 : Ordinal) < epsilonZero by simpa using (finiteNorm 1).1)
  simpa only [Ordinal.opow_one, epsilonZero] using h

theorem two_power_below {a : Ordinal} (ha : a < epsilonZero) :
    (2 : Ordinal) ^ a < epsilonZero := by
  have hω : Ordinal.omega0 ^ a < epsilonZero :=
    (Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr ha
  exact (Ordinal.opow_le_opow_left a
    (show (2 : Ordinal) ≤ Ordinal.omega0 from (Ordinal.natCast_lt_omega0 2).le)).trans_lt hω

theorem value_below {ι : Type} (f : Nat → Nat) (ρ : ι → Ordinal.{0})
    (hρ : ∀ x, ρ x < epsilonZero) (t : Term ι) :
    ParametricSourceSuccessor.denoteWith f ρ t < epsilonZero := by
  induction t with
  | var x => exact hρ x
  | zero => exact zero_lt_epsilonZero
  | one => simpa only [ParametricSourceSuccessor.denoteWith, Nat.cast_one] using (finiteNorm 1).1
  | omega => exact omega_below
  | add a b iha ihb => exact sum_below iha ihb
  | emul a b iha ihb => exact product_below (two_power_below iha) ihb
  | collapse a b iha ihb => exact (finiteNorm _).1

theorem closed_below (f : Nat → Nat) (t : ClosedExpression) : closedValue f t < epsilonZero :=
  value_below f (fun x => nomatch x) (fun x => nomatch x) t

theorem ambient_below (f : Nat → Nat) {Γ : List Ty} (ρ : AdmissibleSubstitution f Γ)
    (t : OrdinalExpression Γ) : expressionValue f ρ t < epsilonZero := by
  apply value_below f (valuation f ρ) _ t
  rintro ⟨τ,x,j⟩
  exact closed_below f (ρ.vector x j)

theorem valueClosure : SelectedPositivityTargets.ValueClosure :=
  ⟨closed_below, fun f _ ρ t => ambient_below f ρ t⟩

end LogicLineages.PermittedControl.SelectedValueClosureProof
