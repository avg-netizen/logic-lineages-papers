module
public import LogicLineages.ModelsAlgebra.PGroups.IntrinsicLowerTargets
public import LogicLineages.ModelsAlgebra.PGroups.IntrinsicNormalForm
public import LogicLineages.ModelsAlgebra.PGroups.FullShiftLimit
public import LogicLineages.ModelsAlgebra.PGroups.ScottTransport
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem intrinsic_no_pi_two_scott : Targets.groupIntrinsicNoPiTwoScott := by
  intro p _ G _ _ k N hk hkN hb hf hi hlo hn φ hφ hscott
  obtain ⟨t,ell,s,r,hell,hr,⟨e⟩⟩ := intrinsic_full_shift_normal_form p G k N hk hkN hb hf hi hlo
  have ht : 0 < t := nonzero_lower_short_block p G k t s ell r
    (fun a => (hell a).2) (fun a => (hr a).1) ⟨e⟩ hn
  have hs := (pi_scott_isomorphism (2 : Ordinal.{0}) G (FullShiftGroup p k t ell s r) e φ hφ).mp hscott
  exact source_finite_blocks_no_pi_two_scott p k t ell s r ht hell (fun a => (hr a).1) φ hφ hs

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
