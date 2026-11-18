import LogicLineages.PersistentMarking.RankedRestrictionCoverageProof

namespace LogicLineages.PersistentMarking.RankedRestrictionMatchingProof
open Spine RankedRestrictionTargets RankedRestrictionSplitProof

inductive WeakMatch (S : Signature) : Args → Args → Prop where
  | nil : WeakMatch S .nil .nil
  | cons : Remove ts t rest → (RPO S q t ∨ Equal q t) → WeakMatch S qs rest →
      WeakMatch S (.cons q qs) ts

def Partition (S : Signature) (bs ts : Args) : Prop :=
  ∃ kept removed matched added,
    Split bs kept removed ∧ Split ts matched added ∧ EqMatch kept matched ∧ RPOCoverage S removed added

def Replacement (S : Signature) (bs ts : Args) : Prop :=
  ∃ kept removed matched added,
    Split bs kept removed ∧ Split ts matched added ∧ Nonempty removed ∧
    EqMatch kept matched ∧ RPOCoverage S removed added

theorem partition (S : Signature) {bs ts : Args} (h : WeakMatch S bs ts) :
    Partition S bs ts := by
  induction h with
  | nil => exact ⟨.nil,.nil,.nil,.nil,.nil,.nil,.nil,.nil⟩
  | cons hRemove hComparison _ ih =>
    obtain ⟨kept,removed,matched,added,hS,hT,hEq,hCover⟩ := ih
    rcases hComparison with hRpo | hEqual
    · obtain ⟨after,hInsert,hSplit⟩ := insertRight hRemove hT
      have hMoved := RankedRestrictionCoverageProof.move S hCover (fun i q h => ⟨i+1,.there h⟩)
      exact ⟨kept,_,matched,after,.right hS,hSplit,hEq,
        RankedRestrictionCoverageProof.insert S hMoved hInsert .here hRpo⟩
    · obtain ⟨after,hInsert,hSplit⟩ := insertLeft hRemove hT
      exact ⟨_,removed,after,added,.left hS,hSplit,.cons hInsert hEqual hEq,hCover⟩

theorem either (S : Signature) {bs ts : Args} (h : WeakMatch S bs ts) :
    Replacement S bs ts ∨ EqMatch bs ts := by
  obtain ⟨kept,removed,matched,added,hS,hT,hEq,hCover⟩ := partition S h
  cases removed with
  | nil =>
    obtain rfl := RankedRestrictionCoverageProof.emptyOwners S added hCover
    exact Or.inr (noRight hS ▸ noRight hT ▸ hEq)
  | cons =>
    exact Or.inl ⟨kept,_,matched,added,hS,hT,trivial,hEq,hCover⟩

theorem replace (S : Signature) {bs ts kept removed matched added : Args}
    (hS : Split bs kept removed) (hT : Split ts matched added) (hN : Nonempty removed)
    (hEq : WeakMatch S kept matched) (hCover : RPOCoverage S removed added) : Replacement S bs ts := by
  obtain ⟨keep,changed,matched',extra,hs,ht,hEq',hCover'⟩ := partition S hEq
  obtain ⟨r,hr,hrSplit⟩ := compose hS hs
  obtain ⟨a,ha,haSplit⟩ := compose hT ht
  exact ⟨keep,r,matched',a,hr,ha,inheritNonempty hrSplit hN,hEq',
    RankedRestrictionCoverageProof.merge S r haSplit
      (RankedRestrictionCoverageProof.move S hCover (fun _ _ h => atLeft hrSplit h))
      (RankedRestrictionCoverageProof.move S hCover' (fun _ _ h => atRight hrSplit h))⟩

theorem target (S : Signature) {bs ts : Args} (h : WeakMatch S bs ts) :
    ∀ i t, At ts i t → ∃ j q, At bs j q ∧ (RPO S q t ∨ Equal q t) := by
  induction h with
  | nil => intro i t hi; cases hi
  | cons hRemove hComp _ ih =>
    intro i t hi
    rcases atRemove hRemove hi with rfl | ⟨j,hj⟩
    · exact ⟨0,_,.here,hComp⟩
    · obtain ⟨k,q,hq,h⟩ := ih j t hj
      exact ⟨k+1,q,.there hq,h⟩

theorem dominates (S : Signature) (q : Expr) (ts : Args) (h : ∀ i t, At ts i t → RPO S q t) :
    Dominates S q ts := by
  cases ts with
  | nil => exact .nil
  | cons t ts => exact .cons (h 0 t .here) (dominates S q ts (fun i t hi => h (i+1) t (.there hi)))
termination_by sizeOf ts

theorem headDominates (S : Signature) (f : Head) (bs ts : Args) (h : WeakMatch S bs ts) :
    Dominates S (.head f bs) ts := by
  apply dominates S _ ts
  intro i t hi
  obtain ⟨j,q,hq,hr|he⟩ := target S h i t hi
  · exact .subtermStrict hq hr
  · exact .subtermEq hq he

end LogicLineages.PersistentMarking.RankedRestrictionMatchingProof
