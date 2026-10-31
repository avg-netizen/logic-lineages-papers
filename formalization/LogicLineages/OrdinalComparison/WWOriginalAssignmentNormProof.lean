module
public import LogicLineages.OrdinalComparison.WWOriginalAssignmentNormTargets
public import LogicLineages.OrdinalComparison.WWOriginalAtomicAssignmentProof
public import LogicLineages.OrdinalComparison.WWOriginalAbstractionNormProof
public import LogicLineages.OrdinalComparison.WWOriginalBoxBoundedProof
public import LogicLineages.OrdinalComparison.WWOriginalGeneratedHeadProof
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalDomain
open AdmissibleSum AdmissibleAssignment

theorem originalSourceApplicationBounded : Targets.OriginalSourceApplicationBounded := by
  intro Γ σ τ p f g gf gg bf bg
  have hnm : σ.level < (Ty.arrow σ τ).level := by
    change σ.level < max (σ.level + 1) τ.level
    have := Nat.le_max_left (σ.level + 1) τ.level
    omega
  obtain ⟨gb, bb⟩ := originalSourceBoxBounded Γ _ _ hnm p f g gf gg bf bg
  constructor
  · intro j
    exact gb ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ (Nat.le_max_right _ _))⟩
  · apply (originalBoundedVectorSupportBridge Γ _ _).mp
    have bb' := (originalBoundedVectorSupportBridge Γ _ _).mpr bb
    intro ρ j
    exact bb' ρ ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ (Nat.le_max_right _ _))⟩

theorem originalSourceAssignmentBounded : Targets.OriginalSourceAssignmentBounded := by
  intro Γ τ p t
  induction t with
  | var x => exact originalVariableAssignmentBounded _ _ p x
  | zeroC =>
    obtain ⟨gv, bv⟩ := originalOneVectorBounded _ _
    exact ⟨_, rfl, gv, bv⟩
  | succC =>
    obtain ⟨gv, bv⟩ := originalOneVectorBounded _ _
    exact ⟨_, rfl, gv, bv⟩
  | caseC σ =>
    obtain ⟨gv, bv⟩ := originalOneVectorBounded _ _
    exact ⟨_, rfl, gv, bv⟩
  | recC σ => exact originalRecursorAssignmentBounded _ σ p
  | @app Γ σ τ f a ihf iha =>
    obtain ⟨vf, hf, gf, bf⟩ := ihf
    obtain ⟨va, ha, ga, ba⟩ := iha
    obtain ⟨gv, bv⟩ := originalSourceApplicationBounded Γ σ τ p vf va gf ga bf ba
    refine ⟨application p vf va, ?_, gv, bv⟩
    simp [assignment, hf, ha]
  | @lam Γ σ τ body ih =>
    obtain ⟨vb, hb, gb, bb⟩ := ih
    obtain ⟨vg, hg, gg⟩ := actualAdmissibleAssignmentGenerated (σ :: Γ) τ p body
    have heq : vg = vb := Option.some.inj (hg.symm.trans hb)
    subst vg
    have gh : ∀ j, HeadGrade Γ σ j.val (vb j) :=
      fun j => originalGeneratedAmbientHead Γ σ j.val (vb j) (gg j) (gb j)
    obtain ⟨v, hv, gv, bv⟩ := originalSourceAbstractionBounded Γ σ τ.level p vb gh bb
    refine ⟨v, ?_, gv, bv⟩
    simp [assignment, hb, hv]
    rfl
  | ranked s args ih => nomatch s

end LogicLineages.OrdinalComparison.Source.OriginalDomain
