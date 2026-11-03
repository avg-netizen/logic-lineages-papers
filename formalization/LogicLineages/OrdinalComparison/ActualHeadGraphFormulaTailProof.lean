module
public import LogicLineages.OrdinalComparison.ActualHeadGraphFormulaTargets
public import LogicLineages.OrdinalComparison.ActualHeadGraphArithmeticProof
public import LogicLineages.OrdinalComparison.GeneralOmegaHeadLimitProof
public import LogicLineages.OrdinalComparison.HeadGraphShiftProof
public import LogicLineages.OrdinalComparison.Control
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.FormulaConstruction.Proof
open ForwardTranslation Arithmetic

private theorem tail_expansion {Γ : List Ty} (q : UnitElimination.Tree Nat (.ground::Γ))
    (a : ClosedPositive) (c : Nat)
    (hq : ∀ (ρ : Variable (.ground::Γ) .ground → Nat) (r : Nat),
      UnitElimination.Eval q ρ r ↔ r=ActualUnaryRay.rayValue a c (ρ .here))
    (δ : Nat) (t y : Expr) (ν : Nat → Nat) :
    (tail q a c δ t y).eval ν ↔ threshold a c δ ≤ t.value ν ∧
      ∃ z v : Nat, ActualUnaryRay.totalNorm a c 0+z=(Phi^[δ]) (t.value ν) ∧
        v=ActualUnaryRay.rayValue a c z ∧ y.value ν=v+δ := by
  simp only [tail,Formula.eval,Expr.value]
  apply and_congr_right
  intro ht
  apply exists_congr
  intro z
  apply exists_congr
  intro v
  simp only [conjunction,List.foldr,Formula.eval]
  rw [Arithmetic.Proof.fixedPhiChain,
    Arithmetic.Proof.unitTreeExpansion (.ground::Γ) q
      (.variable 1 :: List.replicate Γ.length (.numeral 0)) (by simp)]
  rw [hq]
  simp [Arithmetic.Proof.lift_two,Expr.value,extend,inputValues,SourceTypedPorts.variableIndex]

theorem exactTailFromRay : Targets.ExactTailFromRay := by
  intro Γ q a c hq δ t y ν
  rw [tail_expansion q a c hq δ t y ν]
  have hcal := GeneralOmegaHeadLimit.Proof.actualClosedHeadCalibration a
  have hshift := (HeadGraphShift.actual_shift (fixedHead a) hcal.2.2.2.2 hcal.2.2.2.1 δ).2.2.2
  have hnorm (ht : threshold a c δ ≤ t.value ν) :
      actualOrdinalNorm (shiftedHead a δ) ≤ t.value ν :=
    (Nat.le_max_left _ _).trans ht
  have hvalue (ht : threshold a c δ ≤ t.value ν) :
      actualHeadValue (shiftedHead a δ) (t.value ν) =
        actualHeadValue (fixedHead a) ((Phi^[δ]) (t.value ν))+δ :=
    (hshift (t.value ν) (hnorm ht)).2.2.2
  constructor
  · rintro ⟨ht,z,v,hz,hv,hy⟩
    refine ⟨ht,?_⟩
    have hn : ActualUnaryRay.totalNorm a c z = (Phi^[δ]) (t.value ν) := by
      simpa only [ActualUnaryRay.totalNorm,Nat.add_zero] using hz
    rw [hy,hv,ActualUnaryRay.rayValue,hn]
    exact (hvalue ht).symm
  · rintro ⟨ht,hy⟩
    have hiter : t.value ν ≤ (Phi^[δ]) (t.value ν) :=
      iterate_self_le (fun x => (self_lt_Phi x).le) δ (t.value ν)
    have hc : ActualUnaryRay.totalNorm a c 0 ≤ (Phi^[δ]) (t.value ν) :=
      (Nat.le_max_right _ _).trans (ht.trans hiter)
    let z := (Phi^[δ]) (t.value ν)-ActualUnaryRay.totalNorm a c 0
    have hz : ActualUnaryRay.totalNorm a c 0+z=(Phi^[δ]) (t.value ν) := Nat.add_sub_of_le hc
    have hn : ActualUnaryRay.totalNorm a c z = (Phi^[δ]) (t.value ν) := by
      simpa only [ActualUnaryRay.totalNorm,Nat.add_zero] using hz
    refine ⟨ht,z,ActualUnaryRay.rayValue a c z,hz,rfl,?_⟩
    rw [hy,hvalue ht,ActualUnaryRay.rayValue,hn]
end LogicLineages.OrdinalComparison.Source.ActualHeadGraph.FormulaConstruction.Proof
