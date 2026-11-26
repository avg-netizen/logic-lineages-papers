module

public import LogicLineages.NativeModule.PersistentMarking.ActualCollapseCriticalProof

@[expose] public section

/-! Existence and (P): the recursively defined least solution exists at every index `ξ ≤ Λ`.
A clause solution is reached by an ω-iteration: the ordinals below `ξ` with norm below a
countable `θ` are countably many (`normCountable`), so their collapse values have a countable
supremum, above which there is a critical value; the supremum of the iteration is critical. -/

namespace LogicLineages.PersistentMarking.ActualCollapse
open Ordinal Cardinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets
open OrdinalNativeOrbitProof
open scoped Ordinal

/-- Generic: if the clause is solvable whenever the earlier values are critical, the recursive
least solution satisfies (P). -/
theorem collapse_characterization {I : Type*} [LinearOrder I] [WellFoundedLT I]
    (norm : I → Ordinal.{0}) (critical : Ordinal.{0} → Prop) (one : Ordinal.{0}) (endpoint : I)
    (a : ℕ → I)
    (solvable : ∀ (ξ : I) (prev : I → Ordinal.{0}), (∀ η, η < ξ → critical (prev η)) →
      ∃ θ, critical θ ∧ ∀ η, η < ξ → norm η < θ → prev η < θ) :
    CharacterizationP (⟨collapse norm critical, norm, critical, one, endpoint, a⟩ : CollapseData I Ordinal.{0}) := by
  let ψ := collapse norm critical
  have eqn : ∀ ξ, ψ ξ = sInf {θ | critical θ ∧ ∀ η (_ : η < ξ), norm η < θ → ψ η < θ} := by
    intro ξ
    exact WellFounded.fix_eq _ _ ξ
  have mem : ∀ ξ, ψ ξ ∈ {θ | critical θ ∧ ∀ η (_ : η < ξ), norm η < θ → ψ η < θ} := by
    intro ξ
    induction ξ using WellFoundedLT.induction with
    | _ ξ ih =>
      obtain ⟨θ, hθ, hcl⟩ := solvable ξ ψ (fun η h => (ih η h).1)
      rw [eqn ξ]
      exact csInf_mem ⟨θ, hθ, fun η h hn => hcl η h hn⟩
  intro ξ
  refine ⟨(mem ξ).1, fun η h hn => (mem ξ).2 η h hn, fun θ hθ hcl => ?_⟩
  show ψ ξ ≤ θ
  rw [eqn ξ]
  exact csInf_le' ⟨hθ, fun η h hn => hcl η h hn⟩

theorem actualCharacterization : ActualCharacterization := by
  intro N Γ hN hΓ
  obtain ⟨_, below, unbounded, supClosed⟩ := criticalFacts N Γ hN hΓ
  refine collapse_characterization actualNorm (Critical N Γ) 1 actualEndpoint actualArgument ?_
  intro ξ prev hprev
  -- the indices below ξ with norm below t
  let B : Ordinal.{0} → Set ActualIndex := fun t => {η | η < ξ ∧ actualNorm η < t}
  have countB : ∀ t, t < ω₁ → (B t).Countable := by
    intro t ht
    refine (normCountable t ht).preimage_of_injOn (f := Subtype.val) ?_ |>.mono ?_
    · exact Subtype.val_injective.injOn
    · rintro η ⟨h, hn⟩
      exact ⟨lt_of_lt_of_le h ξ.property, hn⟩
  -- the countable supremum of earlier values with small norm
  let sB : Ordinal.{0} → Ordinal.{0} := fun t => ⨆ η : B t, prev η.val
  have sBlt : ∀ t, t < ω₁ → sB t < ω₁ := by
    intro t ht
    haveI : Countable (B t) := (countB t ht).to_subtype
    exact Ordinal.iSup_lt_omega_one (fun η => below _ (hprev η.val η.property.1))
  have sBle : ∀ t η, η < ξ → actualNorm η < t → prev η ≤ sB t := by
    intro t η h hn
    exact le_ciSup (f := fun η : B t => prev η.val)
      ⟨ω₁, fun _ ⟨e, he⟩ => he ▸ (below _ (hprev e.val e.property.1)).le⟩ ⟨η, h, hn⟩
  -- the ω-iteration
  have next : ∀ t, t < ω₁ → ∃ u, Critical N Γ u ∧ max t (sB t) < u := fun t ht =>
    unbounded _ (max_lt ht (sBlt t ht))
  obtain ⟨θ0, c0, -⟩ := unbounded 0 zero_lt_omegaOne
  let step : {t : Ordinal.{0} // Critical N Γ t} → {t : Ordinal.{0} // Critical N Γ t} := fun t =>
    ⟨Classical.choose (next t.val (below _ t.property)),
      (Classical.choose_spec (next t.val (below _ t.property))).1⟩
  have stepGt : ∀ t, max t.val (sB t.val) < (step t).val := fun t =>
    (Classical.choose_spec (next t.val (below _ t.property))).2
  let seq : ℕ → {t : Ordinal.{0} // Critical N Γ t} := fun k => step^[k] ⟨θ0, c0⟩
  have seqSucc : ∀ k, seq (k+1) = step (seq k) := fun k => Function.iterate_succ_apply' step k _
  have mono : StrictMono (fun k => (seq k).val) := by
    refine strictMono_nat_of_lt_succ (fun k => ?_)
    show (seq k).val < (seq (k+1)).val
    rw [seqSucc]
    exact (le_max_left _ _).trans_lt (stepGt _)
  let θ := ⨆ k, (seq k).val
  have bdd : BddAbove (Set.range (fun k => (seq k).val)) := Ordinal.bddAbove_range _
  have lub : IsLUB (Set.range (fun k => (seq k).val)) θ := isLUB_ciSup bdd
  refine ⟨θ, supClosed _ mono (fun k => (seq k).property) θ lub, fun η h hn => ?_⟩
  obtain ⟨k, hk⟩ := (lt_ciSup_iff bdd).1 hn
  have h1 : prev η ≤ sB (seq k).val := sBle _ η h hk
  have h2 : sB (seq k).val < (seq (k+1)).val := by
    rw [seqSucc]
    exact (le_max_right _ _).trans_lt (stepGt _)
  exact h1.trans_lt (h2.trans_le (le_ciSup bdd (k+1)))

end LogicLineages.PersistentMarking.ActualCollapse
