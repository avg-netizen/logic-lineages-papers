module
public import LogicLineages.OrdinalComparison.ParametricPrimitiveLoweringSemanticProof
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Fin
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPrimitiveLowering.Proof
open PrimitiveLowering SourceAdditionCompletion SourceSortCompletion
theorem source_exact (G : Nat → Nat) (hm : StrictMono G) (hi : ∀ n,n ≤ G n)
    {Γ} (ρ : OrdinalComponent Γ → Nat) (g : Gate Γ) (hs : Supported g) (z : Fin 9 → Nat) :
    SourceHolds G ρ g z ↔ g.Holds ρ ∧ z=canonicalWitness ρ g := by
  cases g with
  | eq a b =>
      constructor
      · intro h
        simp only [SourceHolds,lower,all_append,all_cons,all_nil,port_equation G,add_equations_exact G hm hi,successor_aux_identity G hm hi,PrimitiveLowering.Proof.value_liftPort,PrimitiveLowering.Proof.value_aux,unused_holds G,true_and,and_true] at h
        simp [Fin.forall_fin_succ] at h
        refine ⟨h.1,?_⟩
        funext i
        fin_cases i <;> simp [canonicalWitness] <;> omega
      · rintro ⟨h,rfl⟩
        simp only [SourceHolds,lower,all_append,all_cons,all_nil,port_equation G,add_equations_exact G hm hi,successor_aux_identity G hm hi,PrimitiveLowering.Proof.value_liftPort,PrimitiveLowering.Proof.value_aux,unused_holds G,true_and,and_true]
        simpa [canonicalWitness,Fin.forall_fin_succ,Gate.Holds] using h
  | add a b c =>
      constructor
      · intro h
        simp only [SourceHolds,lower,all_append,all_cons,all_nil,port_equation G,add_equations_exact G hm hi,successor_aux_identity G hm hi,PrimitiveLowering.Proof.value_liftPort,PrimitiveLowering.Proof.value_aux,unused_holds G,true_and,and_true] at h
        simp [Fin.forall_fin_succ] at h
        refine ⟨h.1.1,?_⟩
        funext i
        fin_cases i <;> simp [canonicalWitness] <;> omega
      · rintro ⟨h,rfl⟩
        simp only [SourceHolds,lower,all_append,all_cons,all_nil,port_equation G,add_equations_exact G hm hi,successor_aux_identity G hm hi,PrimitiveLowering.Proof.value_liftPort,PrimitiveLowering.Proof.value_aux,unused_holds G,true_and,and_true]
        simpa [canonicalWitness,Fin.forall_fin_succ,Gate.Holds] using h
  | sort a b l h => exact False.elim hs
  | one a =>
      constructor
      · intro h
        simp only [SourceHolds,lower,all_append,all_cons,all_nil,port_equation G,add_equations_exact G hm hi,successor_aux_identity G hm hi,PrimitiveLowering.Proof.value_liftPort,PrimitiveLowering.Proof.value_aux,unused_holds G,true_and,and_true] at h
        simp [Fin.forall_fin_succ] at h
        have ha : a.value ρ=1 := by omega
        refine ⟨ha,?_⟩
        funext i
        fin_cases i <;> simp [canonicalWitness] <;> omega
      · rintro ⟨h,rfl⟩
        simp only [SourceHolds,lower,all_append,all_cons,all_nil,port_equation G,add_equations_exact G hm hi,successor_aux_identity G hm hi,PrimitiveLowering.Proof.value_liftPort,PrimitiveLowering.Proof.value_aux,unused_holds G,true_and,and_true,canonicalWitness]
        simp [Fin.forall_fin_succ,show a.value ρ=1 from h]


theorem sharedInputsAndSyntax : Targets.SharedInputsAndSyntax :=
  ⟨PrimitiveLowering.Proof.sharedInputs,PrimitiveLowering.Proof.primitiveRealization⟩

theorem exactSupportedLowering : Targets.ExactSupportedLowering := by
  intro G hm hi Γ ρ g hs z
  have h := source_exact G hm hi ρ g hs z
  refine ⟨h,?_⟩
  rw [← h]
  unfold ForestHolds forest SourceHolds
  rw [all_map]
  simp only [(PrimitiveLowering.Proof.primitiveRealization _ _).1]

theorem actualGammaLowering : Targets.ActualGammaLowering := by
  intro b Γ ρ g hs
  have hG := ParametricCoefficientOne.Proof.actualGammaCoefficientOne b
  have h := fun z => (exactSupportedLowering _ hG.1 hG.2.1 Γ ρ g hs z).2
  refine ⟨h,?_⟩
  constructor
  · rintro ⟨z,hz⟩
    exact ((h z).mp hz).1
  · intro hg
    exact ⟨canonicalWitness ρ g,(h _).mpr ⟨hg,rfl⟩⟩

theorem exactSize : Targets.ExactSize := by
  intro Γ g _
  exact PrimitiveLowering.Proof.fixedSize Γ g
end LogicLineages.OrdinalComparison.Source.ParametricPrimitiveLowering.Proof
