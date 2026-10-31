module
public import LogicLineages.ModelsAlgebra.PGroups.TerminalFiniteLiftTargets
public import LogicLineages.ModelsAlgebra.PGroups.RetainedSum
public import LogicLineages.ModelsAlgebra.PGroups.RetainedFiltration
public import LogicLineages.ModelsAlgebra.PGroups.FullQuotientFiltration
public import LogicLineages.ModelsAlgebra.PGroups.FiniteBelowLimitExtension
public import LogicLineages.ModelsAlgebra.PGroups.PPrimaryQuotient
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem terminal_finite_lift : Targets.terminalFiniteLift := by
  classical
  intro G _ p _ hG γ A K T hsplit hdis hA D _ hAD
  let δ : Ordinal := Ordinal.omega0 * γ
  let q := QuotientAddGroup.mk' T
  let R := A ⊔ K
  let qR : R →+ G ⧸ T := q.comp R.subtype
  have hqR : Function.Injective qR :=
    retained_sum_quotient_injective G A K T (transfiniteFiltration p δ) hsplit hdis hA
  let e : R ≃+ qR.range := AddMonoidHom.ofInjective hqR
  let E : AddSubgroup (G ⧸ T) := D ⊓ qR.range
  let lift : E →+ G := R.subtype.comp (e.symm.toAddMonoidHom.comp
    (AddSubgroup.inclusion (show E ≤ qR.range from inf_le_right)))
  have hlift : Function.Injective lift := by
    intro x y h
    apply Subtype.ext
    have h' : e.symm ⟨x,x.property.2⟩ = e.symm ⟨y,y.property.2⟩ := Subtype.ext h
    exact congrArg (fun z : qR.range => (z : G ⧸ T)) (e.symm.injective h')
  have hlq (x : E) : q (lift x) = (x:G ⧸ T) := by
    exact congrArg Subtype.val (e.apply_symm_apply ⟨x,x.property.2⟩)
  have hlR (x : E) : lift x ∈ R := (e.symm ⟨x,x.property.2⟩).property
  have hpres (x : E) (β : Ordinal) :
      lift x ∈ (transfiniteFiltration p β : AddSubgroup G) ↔
      (x:G ⧸ T) ∈ (transfiniteFiltration p β : AddSubgroup (G ⧸ T)) := by
    rw [← hlq x]
    exact (retained_filtration_reflection G p δ A K T hsplit hdis hA β (lift x) (hlR x)).symm
  have hhigh : D ⊓ (transfiniteFiltration p δ : AddSubgroup (G ⧸ T)) ≤ E := by
    intro x hx
    refine ⟨hx.1,?_⟩
    obtain ⟨k,hk⟩ := coherent_terminal_quotient G p δ K T hsplit hdis
    let z : K := k.symm ⟨x,hx.2⟩
    refine ⟨⟨z,(le_sup_right : K ≤ R) z.property⟩,?_⟩
    change q (z:G) = x
    rw [← hk z]
    exact congrArg Subtype.val (k.apply_symm_apply ⟨x,hx.2⟩)
  have haE (a : A) : q (a:G) ∈ E :=
    ⟨hAD ⟨a,a.property,rfl⟩,⟨⟨a,(le_sup_left : A ≤ R) a.property⟩,rfl⟩⟩
  have hla (a : A) : lift ⟨q a,haE a⟩ = (a:G) := by
    have heq := hlq ⟨q a,haE a⟩
    exact congrArg Subtype.val (hqR (show qR ⟨lift ⟨q a,haE a⟩,hlR _⟩ =
      qR ⟨a,(le_sup_left : A ≤ R) a.property⟩ from heq))
  by_cases hz : γ=0
  · have hδ : δ=0 := by simp [δ,hz]
    have hDE : D ≤ E := by
      intro x hx
      exact hhigh ⟨hx,by simp [hδ,transfiniteFiltration_zero]⟩
    let F : D →+ G := lift.comp (AddSubgroup.inclusion hDE)
    refine ⟨F,hlift.comp (AddSubgroup.inclusion_injective hDE),?_,?_⟩
    · intro a
      exact hla a
    · intro y β _
      exact hpres ⟨y,hDE y.property⟩ β
  · have hδ : Order.IsSuccLimit δ := Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0
      (lt_of_le_of_ne zero_le (Ne.symm hz))
    have hT : T ≤ (transfiniteFiltration p δ : AddSubgroup G) := by
      rw [hsplit]; exact le_sup_right
    let f : E ≃+ lift.range := AddMonoidHom.ofInjective hlift
    obtain ⟨F,hF,hFa,hFp⟩ := finite_below_limit_extension (G ⧸ T) G p
      (p_primary_quotient G p T hG) hG D E lift.range f δ hδ inf_le_left hhigh
      (fun x β _ => hpres x β)
      (fun α hα => ((full_quotient_filtration p T γ hT).2 α hα).2.symm.le)
    refine ⟨F,hF,?_,hFp⟩
    intro a
    exact (hFa ⟨q a,haE a⟩).trans (hla a)
end LogicLineages.ModelsAlgebra.PGroups
