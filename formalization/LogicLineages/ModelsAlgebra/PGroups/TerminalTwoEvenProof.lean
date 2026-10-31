module
public import LogicLineages.ModelsAlgebra.PGroups.TerminalTwoEvenTargets
public import LogicLineages.ModelsAlgebra.PGroups.TerminalOneOddProof
public import LogicLineages.ModelsAlgebra.PGroups.CutAmalgamationProof
public import LogicLineages.ModelsAlgebra.PGroups.AtomicGeneratedIsoProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupBackAndForth

theorem terminal_two_even_comparison : Targets.terminalTwoEvenComparison := by
  classical
  intro G H _ _ _ _ p _ hG hH rG rH B C _ f γ lG lH hRanks hCuts n b a hbB hbenum hcompat htwo
  let δ : Ordinal := Ordinal.omega0*γ
  let S : AddSubgroup G := transfiniteFiltration p δ
  let U : AddSubgroup H := transfiniteFiltration p δ
  have hδ : δ=0 ∨ Order.IsSuccLimit δ := by
    by_cases hz : γ=0
    · left; simp [δ,hz]
    · right; exact Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 (lt_of_le_of_ne zero_le (Ne.symm hz))
  intro q v
  have heven : 2*γ+2=(2*γ+1)+1 := by rw [add_assoc,one_add_one_eq_two]
  rw [heven]
  apply (back_forth_successor (2*γ+1) H G q _ _).mpr
  intro m d
  let D : AddSubgroup G := B ⊔ AddSubgroup.closure (Set.range d)
  letI : Finite D := p_primary_finite_tuple_extension G p (Fact.out : p.Prime).ne_zero hG B m d
  have hBD : B ≤ D := le_sup_left
  let L : AddSubgroup G := D ⊓ S
  letI : Finite L := Finite.of_injective (AddSubgroup.inclusion (show L≤D from inf_le_left)) (AddSubgroup.inclusion_injective _)
  letI : Fintype L := Fintype.ofFinite L
  let k := Fintype.card L
  let enum : Fin k → L := (Fintype.equivFin L).symm
  let enumS : Fin k → S := fun i => ⟨enum i,(enum i).property.2⟩
  obtain ⟨c,hc⟩ := (back_forth_successor 1 U S n a b).mp
    (by simpa only [one_add_one_eq_two] using htwo) k enumS
  let old : Fin n → L := fun i => ⟨b i,hBD (hbB i),(b i).property⟩
  let bL : Fin (n+k) → L := append old enum
  let bS : Fin (n+k) → S := fun i => ⟨bL i,(bL i).property.2⟩
  let aU : Fin (n+k) → U := append a c
  have hbL : Function.Surjective bL := by
    intro y
    obtain ⟨i,hi⟩ := (Fintype.equivFin L).symm.surjective y
    exact ⟨Fin.natAdd n i,by simpa only [bL,append,Fin.addCases_right,enum] using hi⟩
  have hbS : bS=append b enumS := by
    funext i
    induction i using Fin.addCases with
    | left i => simp only [bS,bL,old,append,Fin.addCases_left]; rfl
    | right i => simp only [bS,bL,enumS,append,Fin.addCases_right]
  have hbf : BackAndForth (1:Ordinal) bS aU := by rw [hbS]; exact hc
  obtain ⟨e0,he0⟩ := (atomic_generated_iso S U (n+k) bS aU).mp (back_forth_atomic 1 S U (n+k) _ _ hbf)
  let R := AddSubgroup.closure (Set.range bS)
  let j : L →+ S := { toFun := fun y => ⟨y,y.property.2⟩, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hjR (y : L) : j y ∈ R := by
    obtain ⟨i,rfl⟩ := hbL y
    exact AddSubgroup.subset_closure ⟨i,rfl⟩
  let jR := j.codRestrict R hjR
  let g : L →+ H := U.subtype.comp ((AddSubgroup.closure (Set.range aU)).subtype.comp (e0.toAddMonoidHom.comp jR))
  have hg : Function.Injective g := by
    intro y z h
    have h₁ := Subtype.ext h
    have h₂ := Subtype.ext h₁
    have h₃ := e0.injective h₂
    exact Subtype.ext (congrArg (fun w : R => (w:S).val) h₃)
  have hdeep (y : L) : g y ∈ U := (e0 (jR y)).val.property
  have hgmatch (i) : g (bL i) = (aU i:H) := by
    have hh := he0 i
    change (e0 (jR (bL i)) : U).val = (aU i:H)
    have hh' : (e0 (jR (bL i)) : U) = aU i := by
      change (e0 ⟨bS i,AddSubgroup.subset_closure ⟨i,rfl⟩⟩ : U) = aU i
      exact hh
    exact congrArg Subtype.val hh'
  let f0 : B →+ H := C.subtype.comp f.toAddMonoidHom
  have hf0 : Function.Injective f0 := by
    intro y z h
    exact f.injective (Subtype.ext h)
  have hagree (y : G) (hy : y∈B) (hl : y∈L) : f0 ⟨y,hy⟩=g ⟨y,hl⟩ := by
    obtain ⟨i,hi⟩ := hbenum y hy hl.2
    subst y
    have hh : g (old i)=(a i:H) := by
      simpa only [bL,aU,append,Fin.addCases_left] using hgmatch (Fin.castAdd k i)
    exact (hcompat i).symm.trans hh.symm
  have hBL : B ⊓ S ≤ L := fun y hy => ⟨hBD hy.1,hy.2⟩
  obtain ⟨F0,hF0,h0B,h0L,h0p⟩ := cut_amalgamation G H p δ B L f0 g hf0 hg inf_le_right hBL hdeep hagree hCuts
  let E : AddSubgroup G := B ⊔ L
  have hED : E ≤ D := sup_le hBD inf_le_left
  have hDE : D ⊓ S ≤ E := le_sup_right
  have hconstruct : ∃ F : D →+ H, Function.Injective F ∧
      (∀ y : E, F ⟨y,hED y.property⟩=F0 y) ∧
      ∀ y : D, ∀ β≤δ, (F y ∈ (transfiniteFiltration p β : AddSubgroup H) ↔
        (y:G) ∈ (transfiniteFiltration p β : AddSubgroup G)) := by
    rcases hδ with hz | hlim
    · have hDL : D ≤ L := fun y hy => ⟨hy,by simp [S,hz,transfiniteFiltration_zero]⟩
      have hD'E : D ≤ E := hDL.trans le_sup_right
      let F := F0.comp (AddSubgroup.inclusion hD'E)
      exact ⟨F,hF0.comp (AddSubgroup.inclusion_injective hD'E),fun _ => rfl,
        fun y β hβ => h0p ⟨y,hD'E y.property⟩ β hβ⟩
    · exact finite_below_limit_extension G H p hG hH D E F0.range (AddMonoidHom.ofInjective hF0)
        δ hlim hED hDE h0p (fun α hα => (hRanks α hα).le)
  obtain ⟨F,hF,hFE,hFp⟩ := hconstruct
  have hFL (y : L) : F ⟨y,y.property.1⟩=g y :=
    (hFE ⟨y,(le_sup_right : L≤E) y.property⟩).trans (h0L y)
  have hFB (y : B) : F ⟨y,hBD y.property⟩=(f y:H) :=
    (hFE ⟨y,(le_sup_left : B≤E) y.property⟩).trans (h0B y)
  let e : D ≃+ F.range := AddMonoidHom.ofInjective hF
  letI : Finite F.range := Finite.of_surjective e e.surjective
  have haR (i) : (aU i:H) ∈ F.range := ⟨⟨bL i,(bL i).property.1⟩,(hFL (bL i)).trans (hgmatch i)⟩
  have haenum (y : H) (hy : y∈F.range) (hyU : y∈U) : ∃ i, (aU i:H)=y := by
    obtain ⟨z,rfl⟩ := hy
    have hz : (z:G) ∈ S := (hFp z δ le_rfl).mp hyU
    obtain ⟨i,hi⟩ := hbL ⟨z,z.property,hz⟩
    refine ⟨i,?_⟩
    have hh := (hFL (bL i)).trans (hgmatch i)
    rw [hi] at hh
    exact hh.symm
  have hnew (i) : (bS i:G)=(e.symm ⟨aU i,haR i⟩:G) := by
    have he : e ⟨bL i,(bL i).property.1⟩=⟨aU i,haR i⟩ := Subtype.ext ((hFL (bL i)).trans (hgmatch i))
    rw [← he,e.symm_apply_apply]
  have hp : MapCutsExact p e.symm δ := by
    intro y β hβ
    have hv : F (e.symm y)=(y:H) := congrArg Subtype.val (e.apply_symm_apply y)
    have hh := hFp (e.symm y) β hβ
    rw [hv] at hh
    exact hh.symm
  have hodd := terminal_one_odd_comparison H G p hH hG rH rG F.range D e.symm γ lH lG
    (fun α hα => (hRanks α hα).symm) hp (n+k) aU bS haR haenum hnew hbf
  have hd (i) : d i∈D := (le_sup_right : AddSubgroup.closure (Set.range d)≤D) (AddSubgroup.subset_closure ⟨i,rfl⟩)
  let t : Fin (q+m) → F.range := append (fun i => e ⟨v i,hBD (v i).property⟩) (fun i => e ⟨d i,hd i⟩)
  have hl : (fun i => (e.symm (t i):G))=append (fun i => (v i:G)) d := by
    funext i
    induction i using Fin.addCases <;> simp only [t,append,Fin.addCases_left,Fin.addCases_right,AddEquiv.symm_apply_apply]
  have hr : (fun i => (t i:H))=append (fun i => (f (v i):H)) (fun i => F ⟨d i,hd i⟩) := by
    funext i
    induction i using Fin.addCases with
    | left i => simp only [t,append,Fin.addCases_left]; exact hFB (v i)
    | right i => simp only [t,append,Fin.addCases_right]; rfl
  have hh := hodd (q+m) t
  change BackAndForth (2*γ+1) (fun i => (e.symm (t i):G)) (fun i => (t i:H)) at hh
  rw [hl,hr] at hh
  exact ⟨fun i => F ⟨d i,hd i⟩,hh⟩
end LogicLineages.ModelsAlgebra.PGroups
