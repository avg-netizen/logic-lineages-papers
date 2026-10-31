module
public import LogicLineages.ModelsAlgebra.PGroups.FiniteEvenResponseTargets
public import LogicLineages.ModelsAlgebra.PGroups.FiniteGapHeadroomProof
public import LogicLineages.ModelsAlgebra.PGroups.FiniteOmegaBoundProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem finite_even_response_extension : Targets.finiteEvenResponseExtension := by
  intro G H _ _ p _ hG hH e he D _ B C f δ hBD hpres hRank
  obtain ⟨N,hN⟩ := finite_omega_block_bound G p D δ
  let lam : Ordinal := δ+(N:Ordinal)
  have hgap : D ⊓ transfiniteFiltration p lam = D ⊓ transfiniteFiltration p (lam+1) := by
    apply (hN N le_rfl).trans
    simpa only [lam,Nat.cast_add,Nat.cast_one,add_assoc] using (hN (N+1) (Nat.le_succ N)).symm
  have hlam : lam < δ+Ordinal.omega0 :=
    (add_lt_add_iff_left δ).mpr (Ordinal.natCast_lt_omega0 N)
  have hbudget : lam+1+(Nat.card D:Ordinal) < δ+Ordinal.omega0 := by
    have h := (add_lt_add_iff_left δ).mpr (Ordinal.natCast_lt_omega0 (N+1+Nat.card D))
    simpa only [lam,Nat.cast_add,Nat.cast_one,add_assoc] using h
  have hcut : lam+1 ≤ δ+Ordinal.omega0 :=
    (Ordinal.le_add_right (lam+1) (Nat.card D:Ordinal)).trans hbudget.le
  obtain ⟨F,hF,hFa,hFp⟩ := finite_gap_response_extension G H p hG hH e he D B C f lam hgap hBD
    (fun b β hβ => hpres b β (hβ.trans hcut))
    (fun b β hβ => (hpres b β (hβ.trans hbudget.le)).mpr)
    (fun α hα => hRank α (hα.trans hlam))
  have hδcut : δ ≤ lam+1 := (Ordinal.le_add_right δ (N:Ordinal)).trans (Order.le_succ lam)
  refine ⟨F,hF,hFa,?_,?_⟩
  · intro z β hβ
    exact hFp z β (hβ.trans hδcut)
  · intro z β hβ hz
    by_cases hβcut : β ≤ lam+1
    · exact (hFp z β hβcut).mp hz
    · have htarget := transfiniteFiltration_antitone p (le_of_not_ge hβcut) hz
      have hsource := (hFp z (lam+1) le_rfl).mp htarget
      have hm : (z:G) ∈ D ⊓ transfiniteFiltration p (δ+((N+1:ℕ):Ordinal)) := by
        refine ⟨z.property,?_⟩
        change (z:G) ∈ transfiniteFiltration p (lam+1) at hsource
        simp only [lam,Nat.cast_add,Nat.cast_one,add_assoc] at hsource ⊢
        exact hsource
      rw [hN (N+1) (Nat.le_succ N)] at hm
      exact transfiniteFiltration_antitone p hβ hm.2

end LogicLineages.ModelsAlgebra.PGroups
