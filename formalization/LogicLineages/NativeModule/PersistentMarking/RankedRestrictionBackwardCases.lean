module

public import LogicLineages.NativeModule.PersistentMarking.RankedRestrictionEqualityProof
public import LogicLineages.NativeModule.PersistentMarking.ElementaryProof

@[expose] public section

namespace LogicLineages.PersistentMarking.RankedRestrictionBackwardCases
open Spine RankedRestrictionTargets RankedRestrictionSyntaxProof

def MarkedGoal (S : Signature) (q t : Expr) : Prop :=
  RankedTerm S q → RankedTerm S t →
    ∃ f bs, q = .head f bs ∧ Weak S (.marked f .ground bs .nil) t

def CoverageGoal (S : Signature) (qs ts : Args) : Prop :=
  ArgsTerm S qs → ArgsTerm S ts → Coverage S qs ts

def DominationGoal (S : Signature) (q : Expr) (ts : Args) : Prop :=
  ∀ f bs, q = .head f bs → RankedTerm S q → ArgsTerm S ts → Whole S f bs .nil ts

theorem toStrict (S : Signature) (q t : Expr) (h : MarkedGoal S q t)
    (hs : RankedTerm S q) (ht : RankedTerm S t) : Strict S q t := by
  obtain ⟨f,bs,rfl,hW⟩ := h hs ht
  exact .intro hs.1 ht.1 (markEq S f bs hs) hW

theorem subterm (S : Signature) (f : Head) (bs : Args) (q t : Expr) (i : Nat) (hAt : At bs i q)
    (ih : RankedTerm S q → RankedTerm S t → Weak S q t) : MarkedGoal S (.head f bs) t := by
  intro hs ht
  have hChild := baseAt S f bs hs i q hAt
  have happ : apply q (ownerCopies f bs .nil []) = some q := rfl
  exact ⟨f,bs,rfl,.select (domains := []) (rootMarked S f bs hs) ht.1 (Or.inl hAt)
    hChild.1.1 happ (ih hChild ht)⟩

theorem subtermEq (S : Signature) (f : Head) (bs : Args) (q t : Expr) (i : Nat)
    (hAt : At bs i q) (he : Equal q t) : MarkedGoal S (.head f bs) t :=
  subterm S f bs q t i hAt (RankedRestrictionEqualityProof.equal S q t he)

theorem subtermStrict (S : Signature) (f : Head) (bs : Args) (q t : Expr) (i : Nat)
    (hAt : At bs i q) (ih : MarkedGoal S q t) : MarkedGoal S (.head f bs) t :=
  subterm S f bs q t i hAt (fun hs ht => ElementaryProof.strictIncluded S q t (toStrict S q t ih hs ht))

theorem precedence (S : Signature) (f g : Head) (bs ts : Args) (hP : Precedes S f g)
    (ih : DominationGoal S (.head f bs) ts) : MarkedGoal S (.head f bs) (.head g ts) := by
  intro hs ht
  have hTy : g.result = .ground := annotation _ ht.2
  have hm : PaperTerm S (.marked f g.result bs .nil) g.result := by
    rw [hTy]
    exact rootMarked S f bs hs
  have hW := Weak.copy hm (hTy.symm ▸ ht.1) hP (ih f bs rfl hs (baseAt S g ts ht))
  rw [hTy] at hW
  exact ⟨f,bs,rfl,hW⟩

theorem multiset (S : Signature) (f : Head) (bs ts kept removed matched added : Args)
    (hS : Split bs kept removed) (hT : Split ts matched added) (hN : Nonempty removed)
    (hE : EqMatch kept matched) (ihC : CoverageGoal S removed added) (ih : DominationGoal S (.head f bs) ts) :
    MarkedGoal S (.head f bs) (.head f ts) := by
  intro hs ht
  have hTy : f.result = .ground := annotation _ hs.2
  have hB := baseAt S f bs hs
  have hTgt := baseAt S f ts ht
  obtain ⟨hK,hR⟩ := RankedRestrictionSyntaxProof.split S hS hB
  obtain ⟨hM,hA⟩ := RankedRestrictionSyntaxProof.split S hT hTgt
  have hMatch := RankedRestrictionEqualityProof.matching S kept matched hE hK hM
  have hm : PaperTerm S (.marked f f.result bs .nil) f.result := by
    rw [hTy]
    exact rootMarked S f bs hs
  obtain ⟨r,hr⟩ := hs.1.2.1
  have hW := Weak.stat hm (hTy.symm ▸ ht.1) ⟨r,hr,hr⟩
    (.replace hS hT hN hMatch (ihC hR hA)) (ih f bs rfl hs hTgt)
  rw [hTy] at hW
  exact ⟨f,bs,rfl,hW⟩

theorem coverNil (S : Signature) (qs : Args) : CoverageGoal S qs .nil := fun _ _ => .nil

theorem coverCons (S : Signature) (qs ts : Args) (q t : Expr) (i : Nat)
    (hAt : At qs i q) (ih : MarkedGoal S q t) (ih' : CoverageGoal S qs ts) :
    CoverageGoal S qs (.cons t ts) := by
  intro hs ht
  exact .cons hAt (toStrict S q t ih (hs i q hAt) (ht 0 t .here))
    (ih' hs (fun j u ha => ht (j+1) u (.there ha)))

theorem domNil (S : Signature) (q : Expr) : DominationGoal S q .nil :=
  fun _ _ _ _ _ => .nil

theorem domCons (S : Signature) (q t : Expr) (ts : Args)
    (ih : MarkedGoal S q t) (ih' : DominationGoal S q ts) : DominationGoal S q (.cons t ts) := by
  intro f bs hq hs ht
  have hTerm := ht 0 t .here
  obtain ⟨g,cs,hHead,hW⟩ := ih hs hTerm
  obtain ⟨rfl,rfl⟩ := Expr.head.inj (hq.symm.trans hHead)
  have hChild : Weak S (.marked f t.type bs .nil) t := by
    rw [annotation _ hTerm.2]
    exact hW
  exact .cons hChild (ih' f bs hq hs (fun i u ha => ht (i+1) u (.there ha)))

end LogicLineages.PersistentMarking.RankedRestrictionBackwardCases
