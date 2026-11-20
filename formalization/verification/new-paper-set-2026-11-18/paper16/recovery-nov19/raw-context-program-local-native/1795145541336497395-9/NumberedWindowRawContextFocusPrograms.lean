module

public import LogicLineages.PersistentMarking.NumberedWindowRawContextProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowPositivePathParserPrograms
import LogicLineages.PersistentMarking.NumberedWindowSyntaxShapePrograms

public section
namespace LogicLineages.PersistentMarking.NumberedWindowRawContextFocusPrograms
open NumberedWindowRawContextAlgorithm
open NumberedWindowPositivePathParserPrograms (equalPrim)
open NumberedWindowSyntaxShapePrograms (pairs)

private theorem cellPrim : Primrec cell := by
  apply (Primrec.nat_casesOn₁ none pairs).of_eq
  intro n
  cases n <;> rfl

private def both (p : Pair) : Option (Pair × Pair) := do
  let left ← cell p.1
  let right ← cell p.2
  pure (left,right)

private theorem bothPrim : Primrec both := by
  have leftCode := cellPrim.comp (Primrec.fst : Primrec (Prod.fst : Pair → Nat))
  have rightCode : Primrec (fun p : Pair × Pair => cell p.1.2) :=
    cellPrim.comp (Primrec.snd.comp Primrec.fst)
  apply (Primrec.option_bind leftCode
    (Primrec.option_map rightCode ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂).to₂).of_eq
  rintro ⟨q,r⟩
  cases hq : cell q <;> cases hr : cell r <;> simp [both,hq,hr]

private def sameHead (p : Pair × Pair) : Option Pair :=
  if p.1.1 == p.2.1 then some (p.1.2,p.2.2) else none

private theorem sameHeadPrim : Primrec sameHead :=
  Primrec.ite (Primrec.eq.comp (equalPrim.comp
    (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)) (Primrec.const true))
    (Primrec.option_some.comp ((Primrec.snd.comp Primrec.fst).pair (Primrec.snd.comp Primrec.snd)))
    (Primrec.const none)

private theorem skipPairPrim : Primrec skipPair := by
  apply ((Primrec.option_bind₁ (Primrec.option_bind₁ sameHeadPrim |>.comp bothPrim))).of_eq
  intro p
  cases p with
  | none => rfl
  | some data =>
    rcases data with ⟨q,r⟩
    cases hq : cell q <;> cases hr : cell r <;> simp [skipPair,both,sameHead,hq,hr]

private theorem skipPrefixTick (i : Nat) (p : Option Pair) :
    skipPair (skipPrefix i p) = skipPrefix i (skipPair p) := by
  induction i generalizing p with
  | zero => rfl
  | succ i ih => exact ih (skipPair p)

private theorem skipPrefixPrim :
    Primrec (fun p : Option Pair × Nat => skipPrefix p.2 p.1) := by
  have step : Primrec₂ (fun (_ : Option Pair) (p : Nat × Option Pair) => skipPair p.2) :=
    skipPairPrim.comp (Primrec.snd.comp Primrec.snd)
  change Primrec₂ (fun p i => skipPrefix i p)
  apply (Primrec.nat_rec Primrec.id step).of_eq
  intro p i
  induction i with
  | zero => rfl
  | succ i ih =>
    change skipPair _ = skipPrefix (i+1) p
    exact (congrArg skipPair ih).trans (skipPrefixTick i p)

private def sameSuffix (p : Pair × Pair) : Option Pair :=
  if p.1.2 == p.2.2 then some (p.1.1,p.2.1) else none

private theorem sameSuffixPrim : Primrec sameSuffix :=
  Primrec.ite (Primrec.eq.comp (equalPrim.comp
    (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)) (Primrec.const true))
    (Primrec.option_some.comp ((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd)))
    (Primrec.const none)

theorem focusPrim : Primrec (fun p : Nat × Nat × Nat => focus p.1 p.2.1 p.2.2) := by
  have skipped := skipPrefixPrim.comp ((Primrec.option_some.comp Primrec.snd).pair Primrec.fst)
  have finish := Primrec.option_bind₁ ((Primrec.option_bind₁ sameSuffixPrim).comp bothPrim)
  apply (finish.comp skipped).of_eq
  rintro ⟨i,q,r⟩
  unfold focus
  cases he : skipPrefix i (some (q,r)) with
  | none => simp [he]
  | some p =>
    rcases p with ⟨a,b⟩
    cases ha : cell a <;> cases hb : cell b <;> simp [he,ha,hb,both,sameSuffix]

end LogicLineages.PersistentMarking.NumberedWindowRawContextFocusPrograms
