module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RankedReflectionTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RankedReflectionSupportProof
open Source Source.SourceMarkedSyntax RecursiveComparison RankedTree RankedPathOrder RankedReflection

def shape {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (p : Packed Symbol arity Gamma) : Nat :=
  match p with
  | ⟨_,.var _⟩ => 0
  | ⟨_,.lam _⟩ => 1
  | ⟨_,.ordinary _ _⟩ => 2
  | ⟨_,.marked _ _ _ _ _⟩ => 3

theorem packShape {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (a : Tree Symbol arity Gamma) : shape (pack a)≠3 := by cases a <;> simp [pack,markedSyntax,shape]

theorem encodedList {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (xs : List (Packed Symbol arity Gamma))
    (h : ∀ p∈xs,∃ t : Tree Symbol arity Gamma,pack t=p) :
    ∃ ts : List (Tree Symbol arity Gamma),xs=ts.map pack := by
  induction xs with
  | nil => exact ⟨[],rfl⟩
  | cons p ps ih =>
    obtain ⟨t,ht⟩ := h p (List.mem_cons_self ..)
    obtain ⟨ts,hs⟩ := ih (fun p hp => h p (List.mem_cons_of_mem _ hp))
    exact ⟨t::ts,by simp only [List.map_cons,ht,hs]⟩

theorem permutationLift {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (ss : List (Tree Symbol arity Gamma)) (ps : List (Packed Symbol arity Gamma))
    (h : (ss.map pack).Perm ps) : ∃ ts : List (Tree Symbol arity Gamma),ps=ts.map pack ∧ ss.Perm ts := by
  obtain ⟨ts,ht⟩ := encodedList ps (by
    intro p hp
    obtain ⟨t,ht,he⟩ := List.mem_map.mp (h.symm.subset hp)
    exact ⟨t,he⟩)
  refine ⟨ts,ht,?_⟩
  rw [ht] at h
  exact (List.map_perm_map_iff (RankedTreeInversionProof.embeddingInjectivity Symbol arity Gamma)).mp h

theorem listPreimages {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (ss : List (Tree Symbol arity Gamma)) (left right : List (Packed Symbol arity Gamma))
    (h : (ss.map pack).Perm (left++right)) :
    ∃ l r : List (Tree Symbol arity Gamma),left=l.map pack ∧ right=r.map pack ∧ ss.Perm (l++r) := by
  obtain ⟨l,hl⟩ := encodedList left (by
    intro p hp
    obtain ⟨t,ht,he⟩ := List.mem_map.mp (h.symm.subset (List.mem_append_left right hp))
    exact ⟨t,he⟩)
  obtain ⟨r,hr⟩ := encodedList right (by
    intro p hp
    obtain ⟨t,ht,he⟩ := List.mem_map.mp (h.symm.subset (List.mem_append_right left hp))
    exact ⟨t,he⟩)
  refine ⟨l,r,hl,hr,?_⟩
  rw [hl,hr,← List.map_append] at h
  exact (List.map_perm_map_iff (RankedTreeInversionProof.embeddingInjectivity Symbol arity Gamma)).mp h

theorem weakMatchNil {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) : WeakMatching above ([] : List (Packed Symbol arity Gamma)) [] := by
  intro a b ha hb
  have ha' : a=[] := by simpa using ha.symm
  have hb' : b=[] := by simpa using hb.symm
  subst a
  subst b
  exact .nil

theorem weakMatchCons {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (s t : Packed Symbol arity Gamma)
    (ss ts : List (Packed Symbol arity Gamma)) (hq : OrdinaryComparison above s t)
    (hr : WeakMatching above ss ts) : WeakMatching above (s::ss) (t::ts) := by
  intro a b ha hb
  cases a with
  | nil => cases ha
  | cons x xs =>
    cases b with
    | nil => cases hb
    | cons y ys =>
      have hs : s=pack x := (List.cons.inj ha).1
      have ht : t=pack y := (List.cons.inj hb).1
      exact .cons (hq x y hs ht) (hr xs ys (List.cons.inj ha).2 (List.cons.inj hb).2)

theorem strictMatching {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (ss ts kept retained removed inserted : List (Packed Symbol arity Gamma))
    (hs : ss.Perm (kept++removed)) (ht : ts.Perm (retained++inserted)) (hn : removed≠[])
    (hk : WeakMatching above kept retained) (hr : Replacements above removed inserted) : StrictMatching above ss ts := by
  intro a b ha hb
  obtain ⟨k,d,hk',hd,ha'⟩ := listPreimages a kept removed (ha ▸ hs)
  obtain ⟨r,i,hr',hi,hb'⟩ := listPreimages b retained inserted (hb ▸ ht)
  apply RankedMultisetNormalizationProof.generalizedMultisetNormalization Symbol arity Gamma above a b k r d i ha' hb'
  · intro hz
    exact hn (by simpa only [hd,hz,List.map_nil])
  · exact hk k r hk' hr'
  · exact hr d i hd hi

theorem matchingMember {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {ss ts : List (Tree Symbol arity Gamma)}
    (h : List.Forall₂ (RankedPathOrder.Weak Symbol arity Gamma above) ss ts) :
    ∀ t∈ts,∃ s∈ss,RankedPathOrder.Weak Symbol arity Gamma above s t := by
  induction h with
  | nil => simp
  | @cons s t ss ts hs hr ih =>
    intro x hx
    rcases List.mem_cons.mp hx with he | hm
    · subst x; exact ⟨s,List.mem_cons_self ..,hs⟩
    · obtain ⟨y,hy,hq⟩ := ih x hm
      exact ⟨y,List.mem_cons_of_mem _ hy,hq⟩

theorem multisetTargetPerm {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {ss ts us : List (Tree Symbol arity Gamma)}
    (h : MultisetGreater Symbol arity Gamma above ss ts) (hp : us.Perm ts) :
    MultisetGreater Symbol arity Gamma above ss us := by
  cases h with
  | replace ss ts kept retained removed inserted hs ht hn hk hr =>
    exact .replace ss us kept retained removed inserted hs (hp.trans ht) hn hk hr

theorem funReflection {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) (f : Symbol)
    (ss ts : Fin (arity f) → Tree Symbol arity Gamma) (matched : List (Tree Symbol arity Gamma))
    (hp : (List.ofFn ts).Perm matched)
    (hm : List.Forall₂ (RankedPathOrder.Weak Symbol arity Gamma above) (List.ofFn ss) matched) :
    RankedPathOrder.Weak Symbol arity Gamma above (.node f ss) (.node f ts) := by
  rcases RankedMultisetNormalizationProof.weakMatchingNormalization Symbol arity Gamma above _ _ hm with he | hg
  · exact .equal _ _ (.node f ss ts matched hp he)
  · apply RankedPathOrder.Weak.greater
    apply Greater.multiset f ss ts (multisetTargetPerm above hg hp)
    intro i
    have ht : ts i∈matched := hp.subset (List.mem_ofFn.mpr ⟨i,rfl⟩)
    obtain ⟨child,hc,hw⟩ := matchingMember above hm (ts i) ht
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp hc
    subst child
    exact .subterm f ss j (ts i) hw

end LogicLineages.OrdinalComparison.TerminationOrdering.RankedReflectionSupportProof
