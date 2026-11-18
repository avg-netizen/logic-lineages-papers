module
public import LogicLineages.PermittedControl.SelectedAtomicAssignmentProof
public import LogicLineages.PermittedControl.SelectedGeneratedHeadProof
public import LogicLineages.PermittedControl.SelectedBoxHeadProof
public import LogicLineages.StandardControlCurrent.PolicyAssignmentStatementChecks

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedCanonicalDomainProof
open OrdinalComparison Source SelectedSourceDomain SelectedBoundedDelta
open Source.AdmissibleSum Source.AdmissibleAssignment Source.OrdinalSyntax Source.SyntaxCode

theorem applicationBounded : SelectedCanonicalDomainTargets.ApplicationBounded := by
  intro ctrl K hctrl Γ σ τ p f g gf gg bf bg
  have hnm : σ.level < (Ty.arrow σ τ).level := by
    change σ.level < max (σ.level + 1) τ.level
    have := Nat.le_max_left (σ.level + 1) τ.level
    omega
  obtain ⟨gb, bb⟩ := SelectedBoxAmbientProof.ambientBox ctrl K hctrl Γ _ _ hnm p f g gf gg bf bg
  constructor
  · intro j
    exact gb ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ (Nat.le_max_right _ _))⟩
  · apply (SelectedBoundedDeltaProof.boundedVectorSupportBridge ctrl Γ _ _).mp
    have bb' := (SelectedBoundedDeltaProof.boundedVectorSupportBridge ctrl Γ _ _).mpr bb
    intro ρ j
    exact bb' ρ ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_succ (Nat.le_max_right _ _))⟩

theorem assignmentBounded (ctrl : Nat → Nat) (K : Nat) (hctrl : SelectedWithThreshold ctrl K)
    (Γ : List Ty) (τ : Ty) (p : Policy) (t : OriginalTerm Γ τ) :
    ∃ v : OrdinalVector Γ τ.level, assignment p t = some v ∧
      (∀ j, AmbientGrade ctrl Γ j.val (v j)) ∧ SourceBoundedVector ctrl v := by
  induction t with
  | var x => exact SelectedAtomicAssignmentProof.variableAssignmentBounded ctrl _ _ p x
  | zeroC =>
    obtain ⟨gv, bv⟩ := SelectedAtomicAssignmentProof.oneVectorBounded ctrl _ _
    exact ⟨_, rfl, gv, bv⟩
  | succC =>
    obtain ⟨gv, bv⟩ := SelectedAtomicAssignmentProof.oneVectorBounded ctrl _ _
    exact ⟨_, rfl, gv, bv⟩
  | caseC σ =>
    obtain ⟨gv, bv⟩ := SelectedAtomicAssignmentProof.oneVectorBounded ctrl _ _
    exact ⟨_, rfl, gv, bv⟩
  | recC σ => exact SelectedAtomicAssignmentProof.recursorAssignmentBounded ctrl _ σ p
  | @app Γ σ τ f a ihf iha =>
    obtain ⟨vf, hf, gf, bf⟩ := ihf
    obtain ⟨va, ha, ga, ba⟩ := iha
    obtain ⟨gv, bv⟩ := applicationBounded ctrl K hctrl Γ σ τ p vf va gf ga bf ba
    refine ⟨application p vf va, ?_, gv, bv⟩
    simp [assignment, hf, ha]
  | @lam Γ σ τ body ih =>
    obtain ⟨vb, hb, gb, bb⟩ := ih
    obtain ⟨vg, hg, gg⟩ := actualAdmissibleAssignmentGenerated (σ :: Γ) τ p body
    have heq : vg = vb := Option.some.inj (hg.symm.trans hb)
    subst vg
    have gh : ∀ j, HeadGrade ctrl Γ σ j.val (vb j) :=
      fun j => SelectedGeneratedHeadProof.generatedAmbientHead ctrl Γ σ j.val (vb j) (gg j) (gb j)
    obtain ⟨v, hv, gv, bv⟩ := SelectedAbstractionBoundedProof.abstractionBounded ctrl K hctrl Γ σ τ.level p vb gh bb
    refine ⟨v, ?_, gv, bv⟩
    simp [assignment, hb, hv]
    rfl
  | ranked s args ih => nomatch s

theorem canonicalAssignment : SelectedCanonicalDomainTargets.CanonicalAssignment := by
  intro ctrl K hctrl Γ τ p t
  obtain ⟨v,hv,gv,bv⟩ := assignmentBounded ctrl K hctrl Γ τ p t
  obtain ⟨w,hw,hcode,gw⟩ := StandardControlCurrent.PolicyAssignmentStatementChecks.full.2.2.1 p Γ τ t
  have he : w = v := Option.some.inj (hw.symm.trans hv)
  subst w
  exact ⟨v,hv,hcode,gw,gv,bv⟩

theorem binderBody : SelectedCanonicalDomainTargets.BinderBody := by
  intro ctrl K hctrl Γ σ τ p body
  obtain ⟨v,hv,hcode,gg,gv,bv⟩ := canonicalAssignment ctrl K hctrl (σ :: Γ) τ p body
  exact ⟨v,hv,fun j => SelectedGeneratedHeadProof.generatedAmbientHead ctrl Γ σ j.val (v j) (gg j) (gv j),bv⟩

theorem fullSelectedCanonicalDomain : SelectedCanonicalDomainTargets.FullSelectedCanonicalDomain :=
  ⟨SelectedGeneratedHeadProof.generatedAmbientHead,SelectedAbstractionBoundedProof.abstractionComposition,
    SelectedAbstractionBoundedProof.abstractionBounded,applicationBounded,canonicalAssignment,binderBody,
    StandardControlCurrent.PolicyAssignmentStatementChecks.full.1,
    StandardControlCurrent.PolicyAssignmentStatementChecks.full.2.1,
    StandardControlCurrent.PolicyAssignmentStatementChecks.full.2.2.2⟩

end LogicLineages.PermittedControl.SelectedCanonicalDomainProof
