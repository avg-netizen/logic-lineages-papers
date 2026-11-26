import LogicLineages.PersistentMarking.AuxiliaryTargets
import LogicLineages.PersistentMarking.ElementarySupportProof
namespace LogicLineages.PersistentMarking.RefinementMarkProof
open Spine NameBridge ElementarySupportProof

theorem markOpenMap (σ : Ty) (x depth : Nat) (q : Expr) :
    mark (substitute (.cons (.free σ x) .nil) depth q) =
      (mark q).map (substitute (.cons (.free σ x) .nil) depth) := by
  cases q with
  | free δ y => rfl
  | bound δ i =>
    by_cases hi : i < depth
    · simp [substitute,hi,mark]
    · cases hn : i-depth with
      | zero => simp [substitute,hi,hn,Args.get,shift,mark]
      | succ n => simp [substitute,hi,hn,Args.get,mark]
  | lam δ body =>
    simp only [substitute,mark,markOpenMap σ x (depth+1) body,Option.map_map]
    rfl
  | head f base => rfl
  | marked f τ base extras => rfl
termination_by sizeOf q

theorem validMark (S : Signature) (q r : Expr) (hv : Valid S q) (hm : mark q = some r) : Valid S r := by
  cases q with
  | free σ x => simp [mark] at hm
  | bound σ i => simp [mark] at hm
  | head f base =>
    simp only [mark,Option.some.injEq] at hm
    subst r
    exact ⟨hv.1,hv.2,True.intro⟩
  | marked f τ base extras =>
    simp only [mark,Option.some.injEq] at hm
    subst r
    exact hv
  | lam σ body =>
    cases hb : mark body with
    | none => simp [mark,hb] at hm
    | some b =>
      simp only [mark,hb,Option.map_some,Option.some.injEq] at hm
      subst r
      exact validMark S body b hv hb
termination_by sizeOf q

theorem markPaper (S : Signature) (q : Expr) (σ : Ty) (r : Expr)
    (h : PaperTerm S q σ) (hm : mark q = some r) : PaperTerm S r σ :=
  ⟨SpineMarkingProof.markTyped EmptyContext q σ r h.1 hm, validMark S q r h.2 hm⟩

theorem reflectTree (S : Signature) (q s r : Expr) (h : RefinementTree S q s)
    (hm : mark s = some r) : ∃ p, mark q = some p ∧ Refines S p r := by
  cases h with
  | var => simp [mark] at hm
  | @head f qs ss hp hs hb =>
    simp only [mark,Option.some.injEq] at hm
    subst r
    refine ⟨.marked f f.result qs .nil,rfl,?_⟩
    exact ⟨.marked (markPaper S _ _ _ hp rfl) (markPaper S _ _ _ hs rfl) hb .nil⟩
  | @marked f τ qb qe sb se hp hs hb he =>
    simp only [mark,Option.some.injEq] at hm
    subst r
    exact ⟨.marked f τ qb qe,rfl,⟨.marked hp hs hb he⟩⟩
  | @abs σ q τ s x hp hs hf hg hchild =>
    cases hsm : mark s with
    | none => simp [mark,hsm] at hm
    | some sr =>
      simp only [mark,hsm,Option.map_some,Option.some.injEq] at hm
      subst r
      have hopen := markSubstitution (.cons (.free σ x) .nil) 0 s sr hsm
      have hdepth := markedSpineDepth (.cons (.free σ x) .nil) 0 s sr hsm
      obtain ⟨po,hpo,href⟩ := reflectTree S (openBody σ x q) (openBody σ x s) (openBody σ x sr) hchild hopen
      cases hqm : mark q with
      | none =>
        have hmap := markOpenMap σ x 0 q
        simp only [hqm,Option.map_none] at hmap
        have hc := hmap.symm.trans hpo
        contradiction
      | some qr =>
        have hmap := markOpenMap σ x 0 q
        simp only [hqm,Option.map_some] at hmap
        have heq : openBody σ x qr = po := Option.some.inj (hmap.symm.trans hpo)
        subst po
        refine ⟨.lam σ qr,by simp only [mark,hqm,Option.map_some],?_⟩
        obtain ⟨hchild'⟩ := href
        have hfp : freeOccurs (σ,x) qr = false := (markNames (σ,x) q qr hqm).symm.trans hf
        have hfs : freeOccurs (σ,x) sr = false := (markNames (σ,x) s sr hsm).symm.trans hg
        exact ⟨.abs (markPaper S _ _ _ hp (by simp only [mark,hqm,Option.map_some]))
          (markPaper S _ _ _ hs (by simp only [mark,hsm,Option.map_some])) hfp hfs hchild'⟩
termination_by spineDepth s
decreasing_by all_goals simp_all [spineDepth,openBody] <;> omega

theorem refinementMarkReflection : AuxiliaryTargets.RefinementMarkReflection := by
  intro S q s r h hm
  obtain ⟨h⟩ := h
  exact reflectTree S q s r h hm
end LogicLineages.PersistentMarking.RefinementMarkProof
