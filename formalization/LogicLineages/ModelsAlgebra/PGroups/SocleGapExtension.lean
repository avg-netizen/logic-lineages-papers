module
public import LogicLineages.ModelsAlgebra.PGroups.SocleGapExtensionTargets
public import LogicLineages.ModelsAlgebra.PGroups.SocleGapRoot
public import LogicLineages.ModelsAlgebra.PGroups.PrimeExtension
public import LogicLineages.ModelsAlgebra.PGroups.ProperExtensionTransport
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u v

theorem socle_gap_preserving_extension : Targets.groupSocleGapPreservingExtension.{u,v} := by
  intro G H _ _ p _ B C _ x α δ hG hH hαδ hxB hpx f hpres hRank hx hxnot hgap hproper
  obtain ⟨w,hpw,hw,hwnot,hwC,hwproper⟩ := socle_gap_suitable_root G H p B C x α hxB hpx f
    (fun b β hβ => hpres b β (hβ.trans hαδ)) hRank hx hxnot hgap hproper
  let g : B →+ H := C.subtype.comp f.toAddMonoidHom
  have hg : Function.Injective g := Subtype.val_injective.comp f.injective
  have hwg : w ∉ g.range := by
    rintro ⟨b,hb⟩
    apply hwC
    rw [← hb]
    exact (f b).property
  obtain ⟨F,hF,hFb,hFx⟩ := prime_order_extension G H p B x hxB hpx g hg w hwg hpw
  refine ⟨F,hF,hFb,?_⟩
  exact proper_extension_transport G H p hG hH B x hpx g w α δ hpres
    hx hxnot hw hwnot hproper (fun b β hb => hwproper (f b) β hb) F hFb hFx

end LogicLineages.ModelsAlgebra.PGroups
