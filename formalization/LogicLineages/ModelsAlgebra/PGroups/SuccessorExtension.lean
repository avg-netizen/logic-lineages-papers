module
public import LogicLineages.ModelsAlgebra.PGroups.SuccessorExtensionTargets
public import LogicLineages.ModelsAlgebra.PGroups.SuccessorRoot
public import LogicLineages.ModelsAlgebra.PGroups.PrimeExtension
public import LogicLineages.ModelsAlgebra.PGroups.ProperExtensionTransport
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u v

theorem successor_preserving_extension : Targets.groupSuccessorPreservingExtension.{u,v} := by
  intro G H _ _ p _ B x α δ hG hH hαδ hxB hpx f hf hpres hx hxnot hpx1 hpxnot hproper hmax
  obtain ⟨w,hpw,hw,hwnot,hwrange,hwproper⟩ :=
    successor_suitable_root G H p B x α hxB hpx f hf
      (fun b β hβ => hpres b β (hβ.trans hαδ))
      hx hxnot hpx1 hpxnot hproper hmax
  obtain ⟨F,hF,hFb,hFx⟩ := prime_order_extension G H p B x hxB hpx f hf w hwrange hpw
  refine ⟨F,hF,hFb,?_⟩
  exact proper_extension_transport G H p hG hH B x hpx f w α δ hpres
    hx hxnot hw hwnot hproper hwproper F hFb hFx

end LogicLineages.ModelsAlgebra.PGroups
