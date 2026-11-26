import LogicLineages.PersistentMarking.AuxiliaryTargets
import LogicLineages.PersistentMarking.ElementarySupportProof
namespace LogicLineages.PersistentMarking.AuxiliaryReflexivityProof
open Spine NameBridge ElementarySupportProof

mutual
 theorem refinementRefl (S : Signature) (q : Expr) (σ : Ty) (hp : PaperTerm S q σ) : Refines S q q := by
  cases q with
  | free δ x => exact ⟨.var⟩
  | bound δ i => cases hp.1 with | bound hi => simp [EmptyContext] at hi
  | lam δ body =>
    cases hp.1 with
    | lam hb =>
      obtain ⟨x,hf,_⟩ := OpeningFoundationProof.freshOpeningExists δ body body
      obtain ⟨htree⟩ := refinementRefl S (openBody δ x body) _ (openingPaper S δ _ x body hp)
      exact ⟨.abs hp hp hf hf htree⟩
  | head f base =>
    cases hp.1 with
    | head hb =>
      obtain ⟨htree⟩ := refinementBasesRefl S base _ hb hp.2.2
      exact ⟨.head hp hp htree⟩
  | marked f τ base extras =>
    cases hp.1 with
    | marked hb he =>
      obtain ⟨hbase⟩ := refinementBasesRefl S base _ hb hp.2.2.1
      obtain ⟨hextras⟩ := refinementExtrasRefl S f base extras extras he hp.2.2.2 (fun i q h => ⟨i,h⟩)
      exact ⟨.marked hp hp hbase hextras⟩
 termination_by nodes q
 decreasing_by all_goals simp_all [nodes,argsNodes,openBody,openNodes] <;> omega
 theorem refinementBasesRefl (S : Signature) (qs : Args) (types : List Ty)
    (ht : BaseTyped EmptyContext qs types) (hv : ValidArgs S qs) :
    _root_.Nonempty (RefinementBasesTree S qs qs) := by
  cases qs with
  | nil => exact ⟨.nil⟩
  | cons q qs =>
    cases ht with
    | cons hq hqs =>
      obtain ⟨hqtree⟩ := refinementRefl S q _ ⟨hq,hv.1⟩
      obtain ⟨hqstree⟩ := refinementBasesRefl S qs _ hqs hv.2
      exact ⟨.cons hqtree hqstree⟩
 termination_by argsNodes qs
 decreasing_by all_goals simp_all [nodes,argsNodes] <;> omega
 theorem refinementExtrasRefl (S : Signature) (f : Head) (base full qs : Args)
    (ht : ExtrasTyped EmptyContext qs) (hv : ValidArgs S qs)
    (occ : ∀ i q, At qs i q → ∃ j, At full j q) :
    _root_.Nonempty (RefinementExtrasTree S f base full qs) := by
  cases qs with
  | nil => exact ⟨.nil⟩
  | cons q qs =>
    cases ht with
    | cons hq hqs =>
      obtain ⟨hqtree⟩ := refinementRefl S q _ ⟨hq,hv.1⟩
      obtain ⟨j,hj⟩ := occ 0 q .here
      obtain ⟨hstree⟩ := refinementExtrasRefl S f base full qs hqs hv.2 (fun i r h => occ (i+1) r (.there h))
      exact ⟨.cons (.existing hj hqtree) hstree⟩
 termination_by argsNodes qs
 decreasing_by all_goals simp_all [nodes,argsNodes] <;> omega
end

theorem retypePaper (S : Signature) (f : Head) (τ ρ : Ty) (base extras : Args)
    (h : PaperTerm S (.marked f τ base extras) τ) : PaperTerm S (.marked f ρ base extras) ρ := by
  cases h.1 with
  | marked hb he => exact ⟨.marked hb he,h.2⟩

theorem refinementRetyping : AuxiliaryTargets.RefinementRetyping := by
  intro S f τ ρ qb qe sb se h
  obtain ⟨h⟩ := h
  cases h with
  | marked hq hs hb he => exact ⟨.marked (retypePaper S f τ ρ qb qe hq) (retypePaper S f τ ρ sb se hs) hb he⟩

mutual
 theorem extendedRefl (S : Signature) (q : Expr) (σ : Ty) (hp : PaperTerm S q σ) : ExtendedWeak S q q := by
  cases q with
  | free δ x => exact ⟨.var⟩
  | bound δ i => cases hp.1 with | bound hi => simp [EmptyContext] at hi
  | lam δ body =>
    cases hp.1 with
    | lam hb =>
      obtain ⟨x,hf,_⟩ := OpeningFoundationProof.freshOpeningExists δ body body
      obtain ⟨htree⟩ := extendedRefl S (openBody δ x body) _ (openingPaper S δ _ x body hp)
      exact ⟨.abs hp hp hf hf htree⟩
  | head f base =>
    cases hp.1 with
    | head hb =>
      obtain ⟨rank,hr⟩ := hp.2.1
      obtain ⟨htree⟩ := extendedMatchingRefl S base _ hb hp.2.2
      exact ⟨.funHead hp hp ⟨rank,hr,hr⟩ rfl htree⟩
  | marked f τ base extras =>
    cases hp.1 with
    | marked hb he =>
      obtain ⟨rank,hr⟩ := hp.2.1
      obtain ⟨hbase⟩ := extendedMatchingRefl S base _ hb hp.2.2.1
      obtain ⟨hextras⟩ := extendedOrderedRefl S extras he hp.2.2.2
      exact ⟨.inHead hp hp ⟨rank,hr,hr⟩ hbase hextras⟩
 termination_by nodes q
 decreasing_by all_goals simp_all [nodes,argsNodes,openBody,openNodes] <;> omega
 theorem extendedMatchingRefl (S : Signature) (qs : Args) (types : List Ty)
    (ht : BaseTyped EmptyContext qs types) (hv : ValidArgs S qs) :
    _root_.Nonempty (ExtendedMatchingTree S qs qs) := by
  cases qs with
  | nil => exact ⟨.matchingNil⟩
  | cons q qs =>
    cases ht with
    | cons hq hqs =>
      obtain ⟨hqtree⟩ := extendedRefl S q _ ⟨hq,hv.1⟩
      obtain ⟨hqstree⟩ := extendedMatchingRefl S qs _ hqs hv.2
      exact ⟨.matchingCons .here hqtree hqstree⟩
 termination_by argsNodes qs
 decreasing_by all_goals simp_all [nodes,argsNodes] <;> omega
 theorem extendedOrderedRefl (S : Signature) (qs : Args)
    (ht : ExtrasTyped EmptyContext qs) (hv : ValidArgs S qs) :
    _root_.Nonempty (ExtendedOrderedTree S qs qs) := by
  cases qs with
  | nil => exact ⟨.orderedNil⟩
  | cons q qs =>
    cases ht with
    | cons hq hqs =>
      obtain ⟨hqtree⟩ := extendedRefl S q _ ⟨hq,hv.1⟩
      obtain ⟨hqstree⟩ := extendedOrderedRefl S qs hqs hv.2
      exact ⟨.orderedCons hqtree hqstree⟩
 termination_by argsNodes qs
 decreasing_by all_goals simp_all [nodes,argsNodes] <;> omega
end

theorem markedStrictSelf : AuxiliaryTargets.MarkedStrictSelf := by
  intro S f τ base extras hp
  obtain ⟨h⟩ := extendedRefl S (.marked f τ base extras) τ hp
  exact ⟨.strictIntro hp hp rfl h⟩
end LogicLineages.PersistentMarking.AuxiliaryReflexivityProof
