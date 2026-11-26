module
public import LogicLineages.PersistentMarking.NumberedWindowRawExchangeSymmetryTargets
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesCodecProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowRawExchangeSymmetryStepProof

open NumberedWindowAnnotationAlgorithm (declaration)
open NumberedWindowExchangeAlgorithm (Row table parts termNext argsNext)
open NumberedWindowExchangeAtoms (HeadPairs allowed bag)
open NumberedWindowFieldAlgorithm (unpack unpackNode)
open NumberedWindowPairAlgorithm (pair decode)
open NumberedWindowRawExchangeVerticesCodecProof (decoded getFieldLt)
open NumberedWindowRawExchangeSymmetryTargets (HeadPairsSymmetric)

abbrev ChildRowsSymmetric (hp : HeadPairs) (a b : Nat) : Prop :=
  ∀ {x y : Nat}, x < a → y < b →
    (table hp (pair a b)).getD (pair x y) (false,false) =
      (table hp (pair b a)).getD (pair y x) (false,false)

private theorem equalityBit (a b : Nat) : (a == b) = (b == a) :=
  Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq]; exact eq_comm)

private theorem bagSymmetric (a b : Nat) : bag a b = bag b a := by
  cases ha : unpack a with
  | none => cases hb : unpack b <;> simp [bag,ha,hb]
  | some xs =>
    cases hb : unpack b with
    | none => simp [bag,ha,hb]
    | some ys =>
      simp only [bag,ha,hb,Option.any_some]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      exact ⟨List.Perm.symm,List.Perm.symm⟩

private theorem partsSymmetric (hp : HeadPairs) (sym : HeadPairsSymmetric hp)
    (before after : List Row) (i j : Nat) (fs gs : List Nat)
    (child : ∀ k,
      before.getD (pair (fs.getD k 0) (gs.getD k 0)) (false,false) =
        after.getD (pair (gs.getD k 0) (fs.getD k 0)) (false,false)) :
    parts hp before i j fs gs = parts hp after j i gs fs := by
  by_cases tags : i = j
  · subst j
    have equal k := equalityBit (fs.getD k 0) (gs.getD k 0)
    have heads := sym (fs.getD 0 0) (gs.getD 0 0)
    have declared := equalityBit (declaration (fs.getD 0 0)).1 (declaration (gs.getD 0 0)).1
    have bags k := bagSymmetric (fs.getD k 0) (gs.getD k 0)
    match i with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | _+7 =>
      simp [parts, equal, child, heads, declared, bags]
  · simp [parts,tags,Ne.symm tags]

theorem termSymmetric (hp : HeadPairs) (sym : HeadPairsSymmetric hp)
    (a b : Nat) (earlier : ChildRowsSymmetric hp a b) :
    termNext hp (table hp (pair a b)) a b = termNext hp (table hp (pair b a)) b a := by
  cases ha : unpackNode a with
  | none => cases hb : unpackNode b <;> simp [termNext,ha,hb]
  | some pa =>
    rcases pa with ⟨i,fs⟩
    cases hb : unpackNode b with
    | none => simp [termNext,ha,hb]
    | some pb =>
      rcases pb with ⟨j,gs⟩
      simp only [termNext,ha,hb,Option.any_some]
      exact partsSymmetric hp sym _ _ i j fs gs
        (fun k => earlier (getFieldLt ha k) (getFieldLt hb k))

theorem argsSymmetric (hp : HeadPairs) (a b : Nat) (earlier : ChildRowsSymmetric hp a b) :
    argsNext (table hp (pair a b)) a b = argsNext (table hp (pair b a)) b a := by
  cases a with
  | zero => cases b <;> rfl
  | succ a =>
    cases b with
    | zero => rfl
    | succ b =>
      cases ha : decode a with
      | none => cases hb : decode b <;> simp [argsNext,ha,hb]
      | some pa =>
        rcases pa with ⟨x,u⟩
        cases hb : decode b with
        | none => simp [argsNext,ha,hb]
        | some pb =>
          rcases pb with ⟨y,v⟩
          obtain ⟨_,xl,ul⟩ := decoded ha
          obtain ⟨_,yl,vl⟩ := decoded hb
          simp only [argsNext,ha,hb,Option.any_some]
          rw [earlier (Nat.lt_succ_of_le xl) (Nat.lt_succ_of_le yl),
            earlier (Nat.lt_succ_of_le ul) (Nat.lt_succ_of_le vl),
            equalityBit u v, equalityBit x y]

end LogicLineages.PersistentMarking.NumberedWindowRawExchangeSymmetryStepProof
