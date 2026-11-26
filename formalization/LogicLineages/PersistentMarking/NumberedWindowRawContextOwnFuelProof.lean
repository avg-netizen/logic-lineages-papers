module
public import LogicLineages.PersistentMarking.NumberedWindowRawContextAlgorithm
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserRawPairProof

public section

namespace LogicLineages.PersistentMarking.NumberedWindowRawContextOwnFuelProof
open NumberedWindowRawContextAlgorithm
open NumberedWindowFieldAlgorithm (pack unpack packNode unpackNode)
open NumberedWindowPairAlgorithm (pair decode)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
  (cellAt emptyUnpack packOfUnpack splitUnpack)
open NumberedWindowInternalSparseFieldParserRawPairProof (decodedPair encodedPair)

private theorem terminal (root : RawRoot) (fuel : Nat) (b : Bool) :
    iterate root fuel (b,none) = (b,none) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => exact ih

private theorem pairBounds (a b : Nat) : a ≤ pair a b ∧ b ≤ pair a b := by
  let s := a+b
  have hs : s ≤ s*s := by
    by_cases z : s = 0
    · rw [z]
    · have one : 1 ≤ s := Nat.pos_of_ne_zero z
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left s one
  have h := Nat.le_trans hs (Nat.le_add_right (s*s) a)
  exact ⟨Nat.le_trans (Nat.le_add_right a b) h,Nat.le_trans (Nat.le_add_left b a) h⟩

private theorem packBelow (xs : List Nat) (w : Nat) (h : w ∈ xs) : w < pack xs := by
  induction xs with
  | nil => cases h
  | cons a xs ih =>
    rcases List.mem_cons.mp h with rfl | tail
    · exact Nat.lt_succ_of_le (pairBounds w (pack xs)).1
    · exact Nat.lt_succ_of_le (Nat.le_trans (Nat.le_of_lt (ih tail)) (pairBounds a (pack xs)).2)

private theorem unpackPack (xs : List Nat) : unpack (pack xs) = some xs := by
  induction xs with
  | nil => exact emptyUnpack
  | cons x xs ih =>
    change unpack (pair x (pack xs) + 1) = _
    rw [splitUnpack (cellAt x (pack xs)),ih]
    rfl

private theorem showNode (tag : Nat) (xs : List Nat) :
    unpackNode (packNode tag xs) = some (tag,xs) := by
  simp [packNode,unpackNode,encodedPair,unpackPack]

private theorem contextChildMem {tag : Nat} {ws : List Nat}
    {a b : Nat × List Nat} {q w r : Nat}
    (h : context tag ws a b = some (q,w,r)) : w ∈ ws := by
  unfold context at h
  split at h
  all_goals try
    split at h
    · first
      | have e := Option.some.inj h
        simp_all
      | obtain ⟨x,hx,he⟩ := Option.map_eq_some_iff.mp h
        have ew := congrArg (fun f : Frame => f.2.1) he
        simp_all
    · cases h
  all_goals contradiction

private theorem nextChildMem {tag : Nat} {ws : List Nat}
    {a b q w r : Nat} (h : next tag ws a b = some (q,w,r)) : w ∈ ws := by
  cases hs : unpackNode a with
  | none => simp [next,hs] at h
  | some src =>
    cases ht : unpackNode b with
    | none => simp [next,hs,ht] at h
    | some dst =>
      exact contextChildMem (a := src) (b := dst) (q := q) (r := r) (by simpa [next,hs,ht] using h)

private theorem parsedRead {p tag : Nat} {ws : List Nat}
    (h : unpackNode p = some (tag,ws)) : packNode tag ws = p := by
  cases p with
  | zero => cases h
  | succ p =>
    cases dec : decode p with
    | none => simp [unpackNode,dec] at h
    | some a =>
      obtain ⟨t,u⟩ := a
      cases body : unpack u with
      | none => simp [unpackNode,dec,body] at h
      | some row =>
        have e : (t,row) = (tag,ws) := Option.some.inj (by simpa [unpackNode,dec,body] using h)
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj e
        rw [packNode,← packOfUnpack u body,decodedPair dec]

/-- Every successful genuine contextual successor, including the opaque
fallback cases of the sparse machine, reads its new witness from an
actual field of the original raw witness. This is about all natural
codes, not just round-trip encodings of a typed syntax tree. -/
theorem exact_ContextWitnessDescends {p a b tag q w r : Nat} {ws : List Nat}
    (hp : unpackNode p = some (tag,ws)) (hn : next tag ws a b = some (q,w,r)) : w < p := by
  rw [← parsedRead hp]
  exact Nat.lt_succ_of_le (Nat.le_trans (Nat.le_of_lt (packBelow ws w (nextChildMem hn)))
    (pairBounds tag (pack ws)).2)

/-- All genuine raw tapes have stable acceptance once their own witness
code has been supplied as fuel. Code zero is explicitly included (the
initial live state need not already be terminal at fuel zero). -/
theorem exact_RawOwnFuelStable (root : RawRoot) (w : Nat) :
    ∀ fuel q r, w ≤ fuel → run root fuel q w r = run root w q w r := by
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro f q r hf
    cases w with
    | zero =>
      cases f with
      | zero => rfl
      | succ f => simp [run,iterate,tick,unpackNode,terminal]
    | succ w =>
      cases f with
      | zero => omega
      | succ f =>
        cases hp : unpackNode (w+1) with
        | none =>
          simp [run,iterate,tick,hp,terminal]
        | some a =>
          obtain ⟨tag,ws⟩ := a
          have equalNext : ∀ s : State, s = (false,next tag ws q r) →
              (iterate root f s).1 = (iterate root w s).1 := by
            rintro s rfl
            cases hn : next tag ws q r with
            | none => simp [terminal]
            | some c =>
              obtain ⟨q',w',r'⟩ := c
              have lt := exact_ContextWitnessDescends hp hn
              have a := ih w' lt f q' r' (by omega)
              have b := ih w' lt w q' r' (by omega)
              exact a.trans b.symm
          change (iterate root f (tick root (false,some (q,w+1,r)))).1 =
            (iterate root w (tick root (false,some (q,w+1,r)))).1
          let dispatch (p : Option (Nat × List Nat)) : State :=
            match p with
            | none => (false,none)
            | some (0,[payload]) => (root q payload r,none)
            | some (tag',fields) => (false,next tag' fields q r)
          change (iterate root f (dispatch (unpackNode (w+1)))).1 =
            (iterate root w (dispatch (unpackNode (w+1)))).1
          rw [hp]
          cases tag with
          | succ tag => exact equalNext _ rfl
          | zero =>
            rcases ws with _ | ⟨payload,_ | ⟨a,rest⟩⟩
            · exact equalNext _ rfl
            · exact congrArg Prod.fst ((terminal root f _).trans (terminal root w _).symm)
            · exact equalNext _ rfl

/-- At every genuine non-root contextual hop the original own-code
run is precisely the child own-code run. This is an equality of raw
acceptance bits, with neither a typing nor a root-calibration premise. -/
theorem exact_RawContextOwnHop (root : RawRoot) {a p b tag q w r : Nat} {ws : List Nat}
    (ht : tag ≠ 0) (hp : unpackNode p = some (tag,ws))
    (hn : next tag ws a b = some (q,w,r)) :
    run root p a p b = run root w q w r := by
  have hw := exact_ContextWitnessDescends hp hn
  cases p with
  | zero => omega
  | succ p =>
    have eqTick : tick root (false,some (a,p+1,b)) = (false,some (q,w,r)) := by
      let dispatch (v : Option (Nat × List Nat)) : State :=
        match v with
        | none => (false,none)
        | some (0,[payload]) => (root a payload b,none)
        | some (tag',fields) => (false,next tag' fields a b)
      change dispatch (unpackNode (p+1)) = _
      rw [hp]
      cases tag with
      | zero => exact False.elim (ht rfl)
      | succ tag => change (false,next (tag+1) ws a b) = _; rw [hn]
    change (iterate root p (tick root (false,some (a,p+1,b)))).1 = _
    rw [eqTick]
    exact exact_RawOwnFuelStable root w p q r (by omega)

/-- Exact own-fuel extraction for the literal selected function-side
application, at arbitrary raw annotations, terms, argument, and child. -/
theorem exact_RawFunctionOwnHop (root : RawRoot) (dom cod arg q w r : Nat) :
    let f := packNode 6 [dom,cod,q,arg]
    let t := packNode 6 [dom,cod,r,arg]
    let p := packNode 5 [w]
    run root p f p t = run root w q w r := by
  dsimp only
  apply exact_RawContextOwnHop root (tag := 5) (ws := [w]) (by decide) (showNode 5 [w])
  simp [next,showNode,context]

#print axioms exact_ContextWitnessDescends
#print axioms exact_RawOwnFuelStable
#print axioms exact_RawContextOwnHop
#print axioms exact_RawFunctionOwnHop
end LogicLineages.PersistentMarking.NumberedWindowRawContextOwnFuelProof
