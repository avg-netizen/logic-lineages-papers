import LogicLineages.PersistentMarking.RefinementOpeningProof
import LogicLineages.PersistentMarking.AuxiliaryReflexivityProof
namespace LogicLineages.PersistentMarking.RefinementTransitivitySupport
open Spine NameBridge RefinementMeasure

theorem annotation {S : Signature} {q s : Expr} (h : RefinementTree S q s) : q.type = s.type := by
  cases h with
  | var => rfl
  | head _ _ _ => rfl
  | marked _ _ _ _ => rfl
  | abs hp hs _ _ _ =>
    exact (SpineShiftProof.annotationExact _ _ _ hp.1).trans (SpineShiftProof.annotationExact _ _ _ hs.1).symm

def retype {S : Signature} {f : Head} {τ : Ty} (ρ : Ty) {qb qe sb se : Args}
    (h : RefinementTree S (.marked f τ qb qe) (.marked f τ sb se)) :
    RefinementTree S (.marked f ρ qb qe) (.marked f ρ sb se) := by
  cases h with
  | marked hp hs hb he =>
    exact .marked (AuxiliaryReflexivityProof.retypePaper S f τ ρ qb qe hp)
      (AuxiliaryReflexivityProof.retypePaper S f τ ρ sb se hs) hb he

theorem pickExtra {S : Signature} {f : Head} {base es qs : Args}
    (h : RefinementExtrasTree S f base es qs) {i : Nat} {q : Expr} (ha : At qs i q) :
    _root_.Nonempty (RefinementExtraTree S f base es q) := by
  cases h with
  | nil => cases ha
  | cons h hs =>
    cases ha with
    | here => exact ⟨h⟩
    | there ha => exact pickExtra hs ha
termination_by sizeOf qs

/- A deliberately universal smaller-right-tree induction hypothesis. Its bound
is the actual all-subtree constructor count, not term syntax or lambda depth. -/
def Smaller (S : Signature) (n : Nat) : Prop := ∀ {q s : Expr} (right : RefinementTree S q s),
  treeSize right < n → ∀ {p : Expr}, RefinementTree S p q → Refines S p s

theorem composeBases (S : Signature) (n : Nat) (ih : Smaller S n)
    (qs ss : Args) (right : RefinementBasesTree S qs ss) (hb : basesSize right < n)
    (ps : Args) (left : RefinementBasesTree S ps qs) :
    _root_.Nonempty (RefinementBasesTree S ps ss) := by
  cases right with
  | nil => cases left; exact ⟨.nil⟩
  | cons r rs =>
    cases left with
    | cons l ls =>
      have hr : treeSize r < n := by change 1 + treeSize r + basesSize rs < n at hb; omega
      have hrs : basesSize rs < n := by change 1 + treeSize r + basesSize rs < n at hb; omega
      obtain ⟨h⟩ := ih r hr l
      obtain ⟨hs⟩ := composeBases S n ih _ _ rs hrs _ ls
      exact ⟨.cons h hs⟩
termination_by sizeOf ss

theorem composeExtra (S : Signature) (n : Nat) (ih : Smaller S n)
    (f : Head) (base es : Args) (s : Expr) (right : RefinementExtraTree S f base es s)
    (hb : extraSize right < n) (pb pe : Args) (τ : Ty)
    (left : RefinementTree S (.marked f τ pb pe) (.marked f τ base es)) :
    _root_.Nonempty (RefinementExtraTree S f pb pe s) := by
  cases right with
  | existing ha r =>
    have hr : treeSize r < n := by change 1 + treeSize r < n at hb; omega
    cases left with
    | marked hp hs hbase hextras =>
      obtain ⟨chosen⟩ := pickExtra hextras ha
      cases chosen with
      | existing ha' l =>
        obtain ⟨h⟩ := ih r hr l
        exact ⟨.existing ha' h⟩
      | owner l =>
        obtain ⟨h⟩ := ih r hr l
        have ht := annotation r
        rw [ht] at h
        exact ⟨.owner h⟩
  | owner r =>
    have hr : treeSize r < n := by change 1 + treeSize r < n at hb; omega
    obtain ⟨h⟩ := ih r hr (retype s.type left)
    exact ⟨.owner h⟩

theorem composeExtras (S : Signature) (n : Nat) (ih : Smaller S n)
    (f : Head) (base es qs : Args) (right : RefinementExtrasTree S f base es qs)
    (hb : extrasSize right < n) (pb pe : Args) (τ : Ty)
    (left : RefinementTree S (.marked f τ pb pe) (.marked f τ base es)) :
    _root_.Nonempty (RefinementExtrasTree S f pb pe qs) := by
  cases right with
  | nil => exact ⟨.nil⟩
  | cons r rs =>
    have hr : extraSize r < n := by change 1 + extraSize r + extrasSize rs < n at hb; omega
    have hrs : extrasSize rs < n := by change 1 + extraSize r + extrasSize rs < n at hb; omega
    obtain ⟨h⟩ := composeExtra S n ih f base es _ r hr pb pe τ left
    obtain ⟨hs⟩ := composeExtras S n ih f base es _ rs hrs pb pe τ left
    exact ⟨.cons h hs⟩
termination_by sizeOf qs

end LogicLineages.PersistentMarking.RefinementTransitivitySupport
