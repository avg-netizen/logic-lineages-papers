module
public import LogicLineages.PermittedControl.SelectedCanonicalDomainTargets
public import LogicLineages.PermittedControl.SelectedBoundedDeltaProof

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedAbstractionBoundedProof
open OrdinalComparison Source SelectedSourceDomain SelectedBoundedDelta
open Source.AdmissibleSum Source.AdmissibleAssignment

theorem abstractionComposition : SelectedCanonicalDomainTargets.AbstractionComposition := by
  intro Γ σ m p h v hv
  unfold LiteralCovariance.delta at hv
  cases hc : collect (m + 1) (fun i => AdmissiblePartial.run p i.val (h i)) with
  | none => simp [hc] at hv
  | some ps =>
    simp only [hc, bind, pure, Option.bind_some, Option.some.injEq] at hv
    subst v
    simp only [abstraction, hc, bind, pure, Option.bind_some]

theorem headClosureVectorBounded (ctrl : Nat → Nat) (Γ : List Ty) (σ : Ty) (m : Nat)
    (h : OrdinalVector (σ :: Γ) m) (hb : SelectedFirstFree.BoundedVector ctrl h) :
    SelectedFirstFree.BoundedVector ctrl (fun j => ordinalHeadClosure (h j)) := by
  intro ρ j
  obtain ⟨ρ', hh, ho⟩ := SelectedHeadClosureProof.headOneExtension ctrl Γ σ ρ
  have hn := hb ρ' j
  rwa [← SelectedHeadClosureProof.headClosureValue ctrl Γ σ ρ ρ' hh ho (h j),
    ← SelectedHeadClosureProof.headClosureValue ctrl Γ σ ρ ρ' hh ho (h 0)] at hn

private theorem add_norm (ctrl : Nat → Nat) {Γ : List Ty} (ρ : AdmissibleSubstitution ctrl Γ) (f g : OrdinalExpression Γ) :
    actualOrdinalNorm (expressionValue ctrl ρ (.add f g)) =
      actualOrdinalNorm (expressionValue ctrl ρ f) + actualOrdinalNorm (expressionValue ctrl ρ g) :=
  Source.OriginalDomain.actualNaturalSumNormAdditivity _ _ (SelectedValueClosureProof.ambient_below ctrl ρ f)
    (SelectedValueClosureProof.ambient_below ctrl ρ g)

theorem abstractionBounded : SelectedCanonicalDomainTargets.AbstractionBounded := by
  intro ctrl K hctrl Γ σ m p h hg hb
  obtain ⟨d, hd, gd, bd⟩ := SelectedBoundedDeltaProof.deltaPreservesBoundedNorm ctrl K hctrl Γ σ m p h hg hb
  have bh := headClosureVectorBounded ctrl Γ σ m h
    ((SelectedBoundedDeltaProof.boundedVectorSupportBridge ctrl (σ :: Γ) m h).mpr hb)
  have bd' := (SelectedBoundedDeltaProof.boundedVectorSupportBridge ctrl Γ _ d).mpr bd
  let v : OrdinalVector Γ (max (σ.level + 1) m) := fun j =>
    if hm : j.val < m + 1 then .add (d j) (ordinalHeadClosure (h ⟨j.val, hm⟩)) else d j
  refine ⟨v, abstractionComposition Γ σ m p h d hd, ?_, ?_⟩
  · intro j
    dsimp only [v]
    split
    · rename_i hm
      exact .add (gd j) (SelectedHeadClosureProof.headClosureGrade ctrl Γ σ j.val _ (hg ⟨j.val, hm⟩))
    · exact gd j
  · apply (SelectedBoundedDeltaProof.boundedVectorSupportBridge ctrl Γ _ v).mp
    intro ρ j
    have hv0 : v 0 = .add (d 0) (ordinalHeadClosure (h 0)) := by simp [v]
    rw [hv0, add_norm]
    by_cases hj : j.val < m + 1
    · simp only [v, dif_pos hj]
      rw [add_norm]
      exact Nat.add_le_add (bd' ρ j) (bh ρ ⟨j.val, hj⟩)
    · simp only [v, dif_neg hj]
      exact (bd' ρ j).trans (Nat.le_add_right _ _)

end LogicLineages.PermittedControl.SelectedAbstractionBoundedProof
