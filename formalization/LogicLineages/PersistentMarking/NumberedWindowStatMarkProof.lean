import LogicLineages.PersistentMarking.NumberedWindowStatTargets
import LogicLineages.PersistentMarking.NumberedWindowStatMarkShapes
import LogicLineages.PersistentMarking.NumberedWindowRawContextFrameBasics
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAnnotationChecks

namespace LogicLineages.PersistentMarking.NumberedWindowStatMarkProof
open NumberedWindowStatAlgorithm NumberedWindowStatTargets NumberedWindowStatMarkShapes
open NumberedWindowSyntax NumberedWindowPrimitiveWitnessBits NumberedWindowRawContextFrameView
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticTyCode
open NumberedWindowArithmeticFields NumberedWindowArithmeticNodeProof
open NumberedWindowRawContextFrameBasics (showNode)
open NumberedWindowRawContextFocusProof (headEq typeEq argsEqCode)
open NumberedWindowArithmeticSyntaxAlgorithmChecks NumberedWindowArithmeticSyntaxAlgorithmTargets
open NumberedWindowArithmeticTermCodeChecks

private theorem atom (a : Atom) : numeric a = symbolic a := by
  cases a with
  | ordinary f bs g t bt et =>
    cases et <;>
      simp [numeric,symbolic,NumberedWindowArithmeticAnnotationProof.head,headEq,typeEq,
        argsEqCode,encodeArgs,Bool.and_assoc]
  | numbered f s k bs es g t l bt et =>
    simp [numeric,symbolic,headEq,typeEq,argsEqCode]

private theorem viewRound (q : NTerm) :
    NumberedWindowFieldAlgorithm.unpackNode (encodeTerm q) = some (view q) := by
  cases q <;> simp [view,encodeTerm,showNode]

private theorem here (Q R : NTerm) :
    markHere (encodeTerm Q,encodeTerm R) = (atoms Q R).any symbolic := by
  unfold markHere
  simp only [viewRound,Option.any]
  rw [numericShape]
  cases atoms Q R <;> simp [Option.any,atom]

private theorem step (Q R : NTerm) :
    peelStep (encodeTerm Q,encodeTerm R) =
      ((lambdas Q R).bind (fun (s,q,t,r) =>
        if s = t then some (encodeTerm q,encodeTerm r) else none)).getD (encodeTerm Q,encodeTerm R) := by
  simp only [peelStep,viewRound,Option.bind_eq_bind,Option.bind_some]
  rw [numericPeel]
  cases h : lambdas Q R with
  | none => rfl
  | some p =>
    rcases p with ⟨s,q,t,r⟩
    simp [typeEq]

private theorem peelTick (n : Nat) (p : Pair) :
    peelStep (peel n p) = peel n (peelStep p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change peelStep (peelStep (peel n p)) = peelStep (peel n (peelStep p))
    rw [ih]

private theorem peelFixed (fuel : Nat) (p : Pair) (h : peelStep p = p) : peel fuel p = p := by
  induction fuel with
  | zero => rfl
  | succ n ih => simp [peel,ih,h]

private theorem termPos (Q : NTerm) : 0 < encodeTerm Q := by
  cases Q <;> exact nodePos _ _

private theorem atFuel (fuel : Nat) (Q R : NTerm) (h : encodeTerm Q ≤ fuel) :
    markHere (peel fuel (encodeTerm Q,encodeTerm R)) = markBit Q R := by
  induction fuel generalizing Q R with
  | zero => have hp := termPos Q; omega
  | succ fuel ih =>
    cases hl : lambdas Q R with
    | none =>
      have hs : peelStep (encodeTerm Q,encodeTerm R) = (encodeTerm Q,encodeTerm R) := by
        simp [step,hl]
      rw [peelFixed _ _ hs,here,symbolicShape,hl]
    | some row =>
      rcases row with ⟨s,q,t,r⟩
      by_cases he : s = t
      · have hp : encodeTerm q < encodeTerm Q := by
          rw [childCode hl]
          exact nodeBelow 2 [encodeTy s,encodeTerm q] (encodeTerm q) (by simp)
        have hs : peelStep (encodeTerm Q,encodeTerm R) = (encodeTerm q,encodeTerm r) := by
          simp [step,hl,he]
        change markHere (peelStep (peel fuel (encodeTerm Q,encodeTerm R))) = _
        rw [peelTick,hs,ih q r (by omega),symbolicShape Q R,hl]
        simp [he]
      · have hs : peelStep (encodeTerm Q,encodeTerm R) = (encodeTerm Q,encodeTerm R) := by
          simp [step,hl,he]
        rw [peelFixed _ _ hs,here,atomicOfLambda hl,symbolicShape,hl]
        simp [he]

theorem markExact : ExactMark := by
  intro q r
  unfold mark
  rw [exact_ExactTermArgsGuards q,exact_ExactTermArgsGuards r]
  simp only [OriginalRow]
  cases hq : decodeTerm q with
  | none => simp
  | some Q =>
    cases hr : decodeTerm r with
    | none => simp
    | some R =>
      have eqQ := (exact_TermCodec.1 q Q).mp hq
      have eqR := (exact_TermCodec.1 r R).mp hr
      simpa [hq,hr,Option.any,eqQ,eqR] using atFuel (encodeTerm Q) Q R (Nat.le_refl _)

end LogicLineages.PersistentMarking.NumberedWindowStatMarkProof
