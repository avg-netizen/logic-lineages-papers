module
public import LogicLineages.OrdinalComparison.ParametricSourceSuccessorTargets
public import LogicLineages.OrdinalComparison.ParametricActualCollapseProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricSourceSuccessor.Proof
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem outside_zero (G : Nat → Nat) (a : Ordinal) (ha : ¬ a < epsilonZero) :
    ParametricActualCollapse.collapseWith G a = 0 := by
  conv_lhs => rw [ParametricActualCollapse.collapseWith,WellFounded.fix_eq]
  simp only [if_neg ha]

theorem phi_global (a : Ordinal) : ParametricActualCollapse.collapseWith Phi a = actualCollapse a := by
  by_cases ha : a < epsilonZero
  · exact ParametricActualCollapse.Proof.exactPhiSpecialization a ha
  · rw [outside_zero Phi a ha]
    symm
    conv_lhs => rw [actualCollapse,WellFounded.fix_eq]
    simp only [if_neg ha]

theorem denote_phi {ι : Type} (ρ : ι → Ordinal)
    (t : LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics.Term ι) :
    denoteWith Phi ρ t = denote ρ t := by
  induction t with
  | var i => rfl
  | zero => rfl
  | one => rfl
  | omega => rfl
  | add a b ia ib => simp only [denoteWith,denote,ia,ib]
  | emul a b ia ib => simp only [denoteWith,denote,ia,ib]
  | collapse a b ia ib => simp only [denoteWith,denote,ia,ib,phi_global]

theorem phiCalibration : Targets.PhiCalibration := ⟨outside_zero,phi_global,fun _ => denote_phi⟩

theorem exactSubstitution : Targets.ExactSubstitution := by
  intro ι κ G ρ σ t
  induction t with
  | var i => rfl
  | zero => rfl
  | one => rfl
  | omega => rfl
  | add a b ia ib => simp only [substitute,denoteWith,ia,ib]
  | emul a b ia ib => simp only [substitute,denoteWith,ia,ib]
  | collapse a b ia ib => simp only [substitute,denoteWith,ia,ib]
end LogicLineages.OrdinalComparison.Source.ParametricSourceSuccessor.Proof
