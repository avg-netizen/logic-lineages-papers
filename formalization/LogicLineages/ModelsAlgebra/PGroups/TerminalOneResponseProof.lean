module
public import LogicLineages.ModelsAlgebra.PGroups.TerminalOneResponseTargets
public import LogicLineages.ModelsAlgebra.PGroups.AtomicGeneratedIsoProof
public import LogicLineages.ModelsAlgebra.PGroups.CutAmalgamationProof
public import LogicLineages.ModelsAlgebra.PGroups.FiniteBelowLimitExtension
public import LogicLineages.ModelsAlgebra.PGroups.BackForthStructuralProof
public import Mathlib.Data.Fintype.EquivFin
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupBackAndForth

theorem terminal_one_response : Targets.terminalOneResponse := by
  classical
  intro G H _ _ p _ hG hH D _ B C f δ hδ hBD hpres hRank n b a hb henum hab hbf
  let S : AddSubgroup G := transfiniteFiltration p δ
  let U : AddSubgroup H := transfiniteFiltration p δ
  let L : AddSubgroup G := D ⊓ S
  letI : Finite L := Finite.of_injective (AddSubgroup.inclusion (show L ≤ D from inf_le_left))
    (AddSubgroup.inclusion_injective _)
  letI : Fintype L := Fintype.ofFinite L
  let m := Fintype.card L
  let dL : Fin m → L := (Fintype.equivFin L).symm
  let d : Fin m → S := fun i => ⟨dL i,(dL i).property.2⟩
  have hd : Function.Surjective dL := (Fintype.equivFin L).symm.surjective
  obtain ⟨c,hc⟩ := (back_forth_successor 0 U S n a b).mp (by simpa only [zero_add] using hbf) m d
  have hac : AtomicAgreement (append b d) (append a c) :=
    back_forth_atomic 0 S U (n+m) _ _ hc
  obtain ⟨e,he⟩ := (atomic_generated_iso S U (n+m) (append b d) (append a c)).mp hac
  let R := AddSubgroup.closure (Set.range (append b d))
  let j : L →+ S := {
    toFun := fun x => ⟨x,x.property.2⟩
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
  have hjR (x : L) : j x ∈ R := by
    obtain ⟨i,rfl⟩ := hd x
    exact AddSubgroup.subset_closure ⟨Fin.natAdd n i,by simp [append,d,j]⟩
  let jR : L →+ R := j.codRestrict R hjR
  let g : L →+ H := U.subtype.comp
    ((AddSubgroup.closure (Set.range (append a c))).subtype.comp (e.toAddMonoidHom.comp jR))
  have hg : Function.Injective g := by
    intro x y h
    have h₁ := Subtype.ext h
    have h₂ := Subtype.ext h₁
    have h₃ := e.injective h₂
    exact Subtype.ext (congrArg (fun z : R => (z:S).val) h₃)
  have hdeep (x : L) : g x ∈ U := (e (jR x)).val.property
  have hmatch (i : Fin n) : g ⟨b i,hBD (hb i),(b i).property⟩ = (a i:H) := by
    have hi := he (Fin.castAdd m i)
    have hi' : e (jR ⟨b i,hBD (hb i),(b i).property⟩) =
        ⟨a i,AddSubgroup.subset_closure ⟨Fin.castAdd m i,by simp [append]⟩⟩ := by
      apply Subtype.ext
      change (e ⟨b i,AddSubgroup.subset_closure ⟨Fin.castAdd m i,by simp [append]⟩⟩ : U) = a i
      simpa only [append,Fin.addCases_left] using hi
    exact congrArg (fun z => (z.val:H)) hi'
  have hagree (x : G) (hxB : x ∈ B) (hxL : x ∈ L) :
      (f ⟨x,hxB⟩:H) = g ⟨x,hxL⟩ := by
    obtain ⟨i,hi⟩ := henum x hxB hxL.2
    subst x
    exact (hab i).symm.trans (hmatch i).symm
  obtain ⟨F,hF,hFB,hFL,hFp⟩ := cut_amalgamation G H p δ B L
    (C.subtype.comp f.toAddMonoidHom) g (Subtype.val_injective.comp f.injective) hg
    inf_le_right (fun x hx => ⟨hBD hx.1,hx.2⟩) hdeep hagree hpres
  let E := B ⊔ L
  have hED : E ≤ D := sup_le hBD inf_le_left
  have hhigh : D ⊓ (transfiniteFiltration p δ : AddSubgroup G) ≤ E := le_sup_right
  rcases hδ with hz | hlim
  · have hDE : D ≤ E := by
      intro x hx
      exact hhigh ⟨hx,by simp [hz,transfiniteFiltration_zero]⟩
    let F' : D →+ H := F.comp (AddSubgroup.inclusion hDE)
    refine ⟨F',hF.comp (AddSubgroup.inclusion_injective hDE),?_,?_⟩
    · intro z; exact hFB z
    · intro y β hβ; exact hFp ⟨y,hDE y.property⟩ β hβ
  · let eF : E ≃+ F.range := AddMonoidHom.ofInjective hF
    obtain ⟨F',hF',hFa',hFp'⟩ := finite_below_limit_extension G H p hG hH D E F.range eF
      δ hlim hED hhigh hFp hRank
    refine ⟨F',hF',?_,hFp'⟩
    intro z
    exact (hFa' ⟨z,(le_sup_left : B ≤ E) z.property⟩).trans (hFB z)
end LogicLineages.ModelsAlgebra.PGroups
