module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarOccurrencesTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarOccurrences.Proof
open ForestParseRepresentationBinary CotreeGrammarShape

theorem wordMembership : Targets.WordMembership := by
  intro I s
  induction s with
  | leaf j => intro i; simp [word, label, Positions, eq_comm]
  | node p q hp hq =>
    intro i
    simp only [word, List.mem_append, hp, hq]
    constructor
    · rintro (⟨x,hx⟩ | ⟨x,hx⟩)
      · exact ⟨.inl x,hx⟩
      · exact ⟨.inr x,hx⟩
    · rintro ⟨x,hx⟩
      cases x with
      | inl x => exact Or.inl ⟨x,hx⟩
      | inr x => exact Or.inr ⟨x,hx⟩

theorem label_mem {I : Type} (s : Shape I) (p : Positions s) : label s p ∈ word s :=
  (wordMembership I s _).mpr ⟨p,rfl⟩

theorem wordNodup : Targets.WordNodup := by
  intro I s
  induction s with
  | leaf i =>
    constructor
    · intro _ a b _; cases a; cases b; rfl
    · intro _; simp [word]
  | node p q hp hq =>
    rw [word, List.nodup_append, hp, hq]
    constructor
    · rintro ⟨ip,iq,hd⟩ x y he
      cases x with
      | inl x =>
        cases y with
        | inl y => exact congrArg Sum.inl (ip he)
        | inr y => exact False.elim ((hd _ (label_mem p x) _ (label_mem q y)) he)
      | inr x =>
        cases y with
        | inl y => exact False.elim ((hd _ (label_mem p y) _ (label_mem q x)) he.symm)
        | inr y => exact congrArg Sum.inr (iq he)
    · intro hi
      refine ⟨?_, ?_, ?_⟩
      · intro x y h; exact Sum.inl.inj (hi (show label (.node p q) (.inl x) = label (.node p q) (.inl y) from h))
      · intro x y h; exact Sum.inr.inj (hi (show label (.node p q) (.inr x) = label (.node p q) (.inr y) from h))
      · intro a ha b hb hab
        rcases (wordMembership I p a).mp ha with ⟨x,rfl⟩
        rcases (wordMembership I q b).mp hb with ⟨y,rfl⟩
        have he := hi (show label (.node p q) (.inl x) = label (.node p q) (.inr y) from hab)
        cases he

theorem occurrencePermutation : Targets.OccurrencePermutation := by
  intro n s
  constructor
  · intro h
    refine ⟨(wordNodup _ s).mp (h.symm.nodup (List.nodup_finRange n)), ?_⟩
    intro i
    exact (wordMembership _ s i).mp (h.mem_iff.mpr (List.mem_finRange i))
  · rintro ⟨hi,hs⟩
    apply (List.perm_ext_iff_of_nodup ((wordNodup _ s).mpr hi) (List.nodup_finRange n)).mpr
    intro i
    exact ⟨fun _ => List.mem_finRange i, fun _ => (wordMembership _ s i).mpr (hs i)⟩

theorem relabel_word {I J : Type} (R : I → J → Prop) (s : Shape I) {l : List J}
    (h : List.Forall₂ R (word s) l) :
    ∃ r : Shape J, Paired R s r ∧ word r = l := by
  induction s generalizing l with
  | leaf i =>
    cases h with
    | cons hij ht =>
      cases ht
      exact ⟨.leaf _, Paired.leaf hij, rfl⟩
  | node p q hp hq =>
    have hl := (List.forall₂_take_append l (word p) (word q) h.flip).flip
    have hr := (List.forall₂_drop_append l (word p) (word q) h.flip).flip
    rcases hp hl with ⟨p',hp',ep⟩
    rcases hq hr with ⟨q',hq',eq⟩
    refine ⟨.node p' q', Paired.node hp' hq', ?_⟩
    simpa only [word, ep, eq] using List.take_append_drop (word p).length l

theorem typeWordReindex : Targets.TypeWordReindex := by
  intro I A n types children s h
  have hf : List.Forall₂ (fun a j => a = children j)
      (List.ofFn children) (List.finRange n) := by
    rw [List.ofFn_eq_map]
    simp only [List.forall₂_map_left_iff]
    generalize List.finRange n = l
    induction l with
    | nil => exact .nil
    | cons i l ih => exact .cons rfl ih
  rcases List.perm_comp_forall₂ h hf with ⟨indices,hm,hp⟩
  have hm' : List.Forall₂ (fun i j => types i = children j) (word s) indices := by
    simpa only [List.forall₂_map_left_iff] using hm
  rcases relabel_word _ s hm' with ⟨r,hr,he⟩
  refine ⟨r,hr,(occurrencePermutation n r).mp ?_⟩
  simpa only [he] using hp

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarOccurrences.Proof
