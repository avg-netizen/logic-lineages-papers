module
public import LogicLineages.ModelsAlgebra.PGroups.FiniteTailTargets
public import LogicLineages.ModelsAlgebra.PGroups.InfiniteStep
public import LogicLineages.ModelsAlgebra.PGroups.UlmFiniteIndependence
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

private theorem finite_ulm_of_rank (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G]
    (S : AddSubgroup G) (hr : Module.rank (ZMod p) (UlmLayer p S) < Cardinal.aleph0) : Finite (UlmLayer p S) := by
  letI modQ : Module (ZMod p) (UlmLayer p S) := inferInstance
  letI freeQ : Module.Free (ZMod p) (UlmLayer p S) := Module.Free.of_divisionRing _ _
  letI finiteQ : Module.Finite (ZMod p) (UlmLayer p S) :=
    (@Module.rank_lt_aleph0_iff (ZMod p) (UlmLayer p S)
      (inferInstance : Semiring (ZMod p)) (inferInstance : AddCommMonoid (UlmLayer p S))
      modQ freeQ inferInstance).mp hr
  exact Cardinal.mk_lt_aleph0_iff.mp
    (@cardinal_lt_aleph0_of_finiteDimensional (ZMod p) (UlmLayer p S)
      (inferInstance : Ring (ZMod p)) inferInstance (inferInstance : AddCommGroup (UlmLayer p S))
      modQ inferInstance freeQ finiteQ)

private theorem finite_ulm_of_finite (p : ℕ) (G : Type) [AddCommGroup G]
    (S : AddSubgroup G) [Finite S] : Finite (UlmLayer p S) := by
  let f : pSocle p S → S := fun x => ⟨x.val,x.property.1⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : S => (z : G)) h)
  letI : Finite (pSocle p S) := Finite.of_injective f hf
  exact Finite.of_surjective (QuotientAddGroup.mk' (successorSocleSubgroup p S))
    (QuotientAddGroup.mk'_surjective (successorSocleSubgroup p S))

theorem finite_tail_from_ranks : Targets.groupFiniteTailFromRanks := by
  intro p _ G _ N hb k hk
  apply Nat.decreasingInduction (n := N)
    (motive := fun j _ => (∀ i : ℕ, j ≤ i → i < N →
      Module.rank (ZMod p) (UlmLayer p (finiteFiltration p i : AddSubgroup G)) < Cardinal.aleph0) →
      Finite (finiteFiltration p j : AddSubgroup G)) ?_ ?_ hk
  · intro j hj ih hr
    have hs : Finite (pStep p (finiteFiltration p j : AddSubgroup G)) :=
      ih (fun i hji hi => hr i ((Nat.le_succ j).trans hji) hi)
    exact finite_step_finite_ulm G p (finiteFiltration p j) hs
      (finite_ulm_of_rank p G (finiteFiltration p j) (hr j le_rfl hj))
  · intro _
    have hbot : finiteFiltration p N = (⊥ : AddSubgroup G) := by
      apply le_antisymm _ bot_le
      intro g hg
      obtain ⟨x,rfl⟩ := (finite_filtration_multiple_image G p N).le hg
      exact hb x
    rw [hbot]
    infer_instance

theorem infinite_ulm_infinite_filtration : Targets.groupInfiniteUlmInfiniteFiltration := by
  intro p _ G _ j hr
  apply not_finite_iff_infinite.mp
  intro hf
  letI : Finite (finiteFiltration p j : AddSubgroup G) := hf
  letI : Finite (UlmLayer p (finiteFiltration p j : AddSubgroup G)) :=
    finite_ulm_of_finite p G (finiteFiltration p j)
  have hlt := (rank_le_card (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G))).trans_lt
    (Cardinal.lt_aleph0_of_finite (UlmLayer p (finiteFiltration p j : AddSubgroup G)))
  rw [hr] at hlt
  exact (lt_irrefl _ hlt)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
