module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowNamedBinding
public import LogicLineages.ComputabilityKnowledge.GorbowSubstitutionSupportProof
public import LogicLineages.ComputabilityKnowledge.GorbowStandardInstancesProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowNamedBindingProof
open GorbowSyntax GorbowFreeSupport GorbowFormulaSubstitution GorbowStandardInstances GorbowNamedBinding

private theorem bindValuation {n : Nat} (v : Fin n) (I : Interpretation) (ρ : Fin n → Nat) (x : Nat) :
    (fun i => (bindDictionary v i).realize I (Fin.cases x ρ)) = assignAt ρ v x := by
  funext i
  by_cases hi : i=v <;> simp [bindDictionary,assignAt,hi,Term.realize]

theorem bindingSemantics : Comparators.GorbowNamedBinding.BindingSemantics := by
  intro n v φ I ρ
  constructor
  · apply forall_congr'
    intro x
    have h := substituteFormula_realize φ I (Fin.cases x ρ) (bindDictionary v)
    simpa only [bindValuation] using h
  · apply exists_congr
    intro x
    have h := substituteFormula_realize φ I (Fin.cases x ρ) (bindDictionary v)
    simpa only [bindValuation] using h

private theorem bindingUses {n : Nat} (v : Fin n) (φ : Formula n) (j : Fin n) :
    (bindAll v φ).uses j=true ↔ φ.uses j=true ∧ j≠v := by
  change (substituteFormula (bindDictionary v) φ).uses j.succ=true ↔ _
  rw [GorbowSubstitutionSupportProof.formulaUses n (n+1) (bindDictionary v) φ j.succ]
  constructor
  · rintro ⟨i,hi,hs⟩
    by_cases hiv : i=v
    · simp [bindDictionary,hiv,Term.uses,Fin.succ_ne_zero] at hs
    · have he : j.succ=i.succ := by simpa [bindDictionary,hiv,Term.uses] using hs
      have hji : j=i := Fin.succ_inj.mp he
      subst i
      exact ⟨hi,hiv⟩
  · rintro ⟨hj,hne⟩
    exact ⟨j,hj,by simp [bindDictionary,hne,Term.uses]⟩

private theorem allSupport {n : Nat} (v : Fin n) (φ : Formula n) :
    formulaSupport (bindAll v φ) = (formulaSupport φ).erase v.val := by
  ext j
  by_cases hj : j<n
  · let k : Fin n := ⟨j,hj⟩
    have ha := GorbowFreeSupportProof.usesCalibration.2 n (bindAll v φ) k
    have hb := GorbowFreeSupportProof.usesCalibration.2 n φ k
    change j ∈ formulaSupport (bindAll v φ) ↔ _ at ha
    change j ∈ formulaSupport φ ↔ _ at hb
    rw [ha,bindingUses,Finset.mem_erase,hb]
    constructor
    · rintro ⟨hu,hne⟩
      exact ⟨fun h => hne (Fin.ext h),hu⟩
    · rintro ⟨hne,hu⟩
      exact ⟨hu,fun h => hne (congrArg Fin.val h)⟩
  · constructor
    · intro h
      exact False.elim (hj (GorbowFreeSupportProof.supportBound.2 n _ j h))
    · intro h
      exact False.elim (hj (GorbowFreeSupportProof.supportBound.2 n φ j (Finset.mem_of_mem_erase h)))

theorem bindingSupport : Comparators.GorbowNamedBinding.BindingSupport := by
  intro n v φ
  have h := allSupport v φ
  exact ⟨h,h⟩

theorem selectionSupport : Comparators.GorbowNamedBinding.SelectionSupport := by
  intro n v φ hφ
  have hv : φ.uses v=true := (GorbowFreeSupportProof.usesCalibration.2 n φ v).mp (by simp [hφ])
  have hu : (selectVariable v φ).uses 0=true :=
    (GorbowSubstitutionSupportProof.formulaUses n 1 (selectDictionary v) φ 0).mpr
      ⟨v,hv,by simp [selectDictionary,Term.uses]⟩
  refine ⟨?_,hu⟩
  have hm := (GorbowFreeSupportProof.usesCalibration.2 1 (selectVariable v φ) 0).mpr hu
  ext j
  constructor
  · intro hj
    have hb := GorbowFreeSupportProof.supportBound.2 1 (selectVariable v φ) j hj
    have hz : j=0 := by omega
    simp [hz]
  · intro hj
    have hz : j=0 := by simpa using hj
    subst j
    exact hm

theorem selectionSemantics : Comparators.GorbowNamedBinding.SelectionSemantics := by
  intro n v φ hφ I ρ
  have hs := substituteFormula_realize φ I (Fin.cases (ρ v) Fin.elim0) (selectDictionary v)
  apply hs.trans
  apply GorbowFreeSupportProof.semanticLocality.2 n φ I _ ρ
  intro i hi
  have hiv : i=v := Fin.ext (by simpa [hφ] using hi)
  subst i
  simp [selectDictionary,Term.realize]

theorem quantifierCalibration : Comparators.GorbowNamedBinding.QuantifierCalibration := by
  intro n v φ hφ I ρ
  constructor
  · apply (bindingSemantics n v φ I ρ).1.trans
    apply forall_congr'
    intro x
    have h := selectionSemantics n v φ hφ I (assignAt ρ v x)
    simpa [assignAt] using h.symm
  · apply (bindingSemantics n v φ I ρ).2.trans
    apply exists_congr
    intro x
    have h := selectionSemantics n v φ hφ I (assignAt ρ v x)
    simpa [assignAt] using h.symm

theorem closedInstanceCalibration : Comparators.GorbowNamedBinding.ClosedInstanceCalibration := by
  intro n v φ hφ t I ρ
  apply (GorbowStandardInstancesProof.literalInstantiation 0 (selectVariable v φ) t I Fin.elim0).trans
  have h := selectionSemantics n v φ hφ I (assignAt ρ v (t.realize I Fin.elim0))
  simpa [assignAt] using h

theorem gorbowNamedBinding : Comparators.GorbowNamedBinding.Target :=
  ⟨bindingSemantics,bindingSupport,selectionSupport,selectionSemantics,quantifierCalibration,closedInstanceCalibration⟩
end LogicLineages.ComputabilityKnowledge.GorbowNamedBindingProof
