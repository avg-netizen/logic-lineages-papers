module
public import LogicLineages.ModelsAlgebra.PGroups.CosetNormalizationTargets
public import LogicLineages.ModelsAlgebra.PGroups.FiltrationProfile
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Finset.Insert
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u v

private theorem finite_total_maximum {I : Type*} [Finite I] [Nonempty I]
    (r : I → I → Prop) (ht : ∀ a b, r a b ∨ r b a)
    (htr : ∀ a b c, r a b → r b c → r a c) : ∃ b, ∀ a, r a b := by
  classical
  letI := Fintype.ofFinite I
  have hrefl (a : I) : r a a := (ht a a).elim id id
  have aux : ∀ s : Finset I, s.Nonempty → ∃ b ∈ s, ∀ a ∈ s, r a b := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      intro _
      by_cases hs : s.Nonempty
      · obtain ⟨b,hb,hmax⟩ := ih hs
        rcases ht a b with hab | hba
        · refine ⟨b,Finset.mem_insert_of_mem hb,?_⟩
          intro c hc
          rcases Finset.mem_insert.mp hc with rfl | hc
          · exact hab
          · exact hmax c hc
        · refine ⟨a,Finset.mem_insert_self a s,?_⟩
          intro c hc
          rcases Finset.mem_insert.mp hc with rfl | hc
          · exact hrefl _
          · exact htr c b a (hmax c hc) hba
      · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        subst s
        exact ⟨a,by simp,by simpa using hrefl a⟩
  obtain ⟨b,_,hb⟩ := aux Finset.univ Finset.univ_nonempty
  exact ⟨b,fun a => hb a (Finset.mem_univ a)⟩

theorem coset_profile_maximum : Targets.groupCosetProfileMaximum.{u,v} := by
  intro G _ p B _ x
  exact finite_total_maximum
    (fun b c : B => ∀ α : Ordinal.{v},
      x + b ∈ (transfiniteFiltration p α : AddSubgroup G) →
      x + c ∈ (transfiniteFiltration p α : AddSubgroup G))
    (fun b c => filtration_profile_total G p (x+b) (x+c))
    (fun a b c hab hbc α hx => hbc α (hab α hx))

theorem coset_double_maximum : Targets.groupCosetDoubleMaximum.{u,v} := by
  classical
  intro G _ p B _ x
  let maximal (b : B) : Prop := ∀ c : B, ∀ α : Ordinal.{v},
    x + c ∈ (transfiniteFiltration p α : AddSubgroup G) →
    x + b ∈ (transfiniteFiltration p α : AddSubgroup G)
  obtain ⟨b,hb⟩ := coset_profile_maximum G p B x
  letI : Nonempty {b : B // maximal b} := ⟨⟨b,hb⟩⟩
  obtain ⟨c,hc⟩ := finite_total_maximum
    (fun b c : {b : B // maximal b} => ∀ α : Ordinal.{v},
      p • (x + b.val) ∈ (transfiniteFiltration p α : AddSubgroup G) →
      p • (x + c.val) ∈ (transfiniteFiltration p α : AddSubgroup G))
    (fun b c => filtration_profile_total G p (p • (x+b.val)) (p • (x+c.val)))
    (fun a b c hab hbc α hx => hbc α (hab α hx))
  exact ⟨c.val,c.property,fun d hd => hc ⟨d,hd⟩⟩

end LogicLineages.ModelsAlgebra.PGroups
