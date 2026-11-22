module

public import LogicLineages.PersistentMarking.NumberedWindowAuxExchangeLiftTargets
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationTableProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesCodecProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowAuxExchangeLiftTypingProof
open NumberedWindowAtomicApplicationTargets (auxRaw)
open NumberedWindowAtomicApplicationTableProof (auxView)
open NumberedWindowAuxExchangeLiftTargets
open NumberedWindowRawExchangeVerticesCodecProof (nodeBounds)

private theorem tableLookup {α : Type} (table : Nat → List α) (cell : Nat → List α → α)
    (empty : table 0 = []) (step : ∀ n, table (n+1) = table n ++ [cell n (table n)])
    (fallback : α) {i n : Nat} (lt : i < n) :
    (table n).getD i fallback = cell i (table i) := by
  have length (n : Nat) : (table n).length = n := by
    induction n with
    | zero => simp [empty]
    | succ n ih => simp [step n,ih]
  rw [List.getD_eq_getElem?_getD]
  have exactCell : (table n)[i]? = some (cell i (table i)) := by
    induction n with
    | zero => omega
    | succ n ih =>
      by_cases prior : i < n
      · rw [step n,List.getElem?_append_left (length n ▸ prior)]
        exact ih prior
      · obtain rfl : i = n := by omega
        rw [step n]
        simpa only [length n] using
          (List.getElem?_concat_length (l := table n) (a := cell n (table n)))
  rw [exactCell]
  rfl

private theorem fnBelow (dom cod fn arg : Nat) : fn < auxRaw dom cod fn arg :=
  (nodeBounds (auxView dom cod fn arg)).2 _ (by simp)

private theorem argBelow (dom cod fn arg : Nat) : arg < auxRaw dom cod fn arg :=
  (nodeBounds (auxView dom cod fn arg)).2 _ (by simp)


/-- Exact original syntax-guard result on every numeric application. -/
theorem syntaxAux : ExactAuxTermSyntax := by
  intro dom cod fn arg
  let q := auxRaw dom cod fn arg
  have fnCell := tableLookup NumberedWindowSyntaxAlgorithm.table (fun n t => (NumberedWindowSyntaxAlgorithm.termNext n t,NumberedWindowSyntaxAlgorithm.argsNext n t))
    rfl (fun _ => rfl) (false,false) (fnBelow dom cod fn arg)
  have argCell := tableLookup NumberedWindowSyntaxAlgorithm.table (fun n t => (NumberedWindowSyntaxAlgorithm.termNext n t,NumberedWindowSyntaxAlgorithm.argsNext n t))
    rfl (fun _ => rfl) (false,false) (argBelow dom cod fn arg)
  change NumberedWindowSyntaxAlgorithm.termNext q (NumberedWindowSyntaxAlgorithm.table q) = _
  simp [-List.getD_eq_getElem?_getD,NumberedWindowSyntaxAlgorithm.termNext,NumberedWindowSyntaxAlgorithm.termParts,q,auxView,fnCell,argCell,NumberedWindowSyntaxAlgorithm.syntaxBits]

private theorem rawAdmission (w : NumberedWindowAdmissionAlgorithm.Window) (dom cod fn arg : Nat) :
    (NumberedWindowAdmissionAlgorithm.rawBits w (auxRaw dom cod fn arg)).1 =
      (w.1.contains cod && w.1.contains dom && (NumberedWindowAdmissionAlgorithm.rawBits w fn).1 && (NumberedWindowAdmissionAlgorithm.rawBits w arg).1) := by
  let q := auxRaw dom cod fn arg
  have fnCell := tableLookup (NumberedWindowAdmissionAlgorithm.table w) (fun n t => (NumberedWindowAdmissionAlgorithm.termNext w n t,NumberedWindowAdmissionAlgorithm.argsNext n t))
    rfl (fun _ => rfl) (false,false) (fnBelow dom cod fn arg)
  have argCell := tableLookup (NumberedWindowAdmissionAlgorithm.table w) (fun n t => (NumberedWindowAdmissionAlgorithm.termNext w n t,NumberedWindowAdmissionAlgorithm.argsNext n t))
    rfl (fun _ => rfl) (false,false) (argBelow dom cod fn arg)
  change NumberedWindowAdmissionAlgorithm.termNext w q (NumberedWindowAdmissionAlgorithm.table w q) = _
  simp [-List.getD_eq_getElem?_getD,-List.contains_eq_mem,NumberedWindowAdmissionAlgorithm.termNext,NumberedWindowAdmissionAlgorithm.termParts,q,auxView,
    fnCell,argCell,NumberedWindowAdmissionAlgorithm.rawBits]

private theorem annotation (dom cod fn arg : Nat) : (NumberedWindowAnnotationAlgorithm.annotations (auxRaw dom cod fn arg)).1 = cod := by
  simp [NumberedWindowAnnotationAlgorithm.annotations,NumberedWindowAnnotationAlgorithm.termNext,NumberedWindowAnnotationAlgorithm.termParts,auxView]

private theorem requirementsAux (dom cod fn arg : Nat) :
    (NumberedWindowLexicalAlgorithm.requirements (auxRaw dom cod fn arg)).1 =
      NumberedWindowLexicalAlgorithm.join (NumberedWindowLexicalAlgorithm.restrict ((NumberedWindowAnnotationAlgorithm.annotations fn).1 == NumberedWindowAnnotationAlgorithm.arrow dom cod) (NumberedWindowLexicalAlgorithm.requirements fn).1)
        (NumberedWindowLexicalAlgorithm.restrict ((NumberedWindowAnnotationAlgorithm.annotations arg).1 == dom) (NumberedWindowLexicalAlgorithm.requirements arg).1) := by
  let q := auxRaw dom cod fn arg
  have fnCell := tableLookup NumberedWindowLexicalAlgorithm.table (fun n t => (NumberedWindowLexicalAlgorithm.termNext n t,NumberedWindowLexicalAlgorithm.argsNext n t))
    rfl (fun _ => rfl) default (fnBelow dom cod fn arg)
  have argCell := tableLookup NumberedWindowLexicalAlgorithm.table (fun n t => (NumberedWindowLexicalAlgorithm.termNext n t,NumberedWindowLexicalAlgorithm.argsNext n t))
    rfl (fun _ => rfl) default (argBelow dom cod fn arg)
  change NumberedWindowLexicalAlgorithm.termNext q (NumberedWindowLexicalAlgorithm.table q) = _
  simp [-List.getD_eq_getElem?_getD,NumberedWindowLexicalAlgorithm.termNext,NumberedWindowLexicalAlgorithm.termParts,q,auxView,fnCell,argCell,NumberedWindowLexicalAlgorithm.requirements]

private theorem holdsJoin (C : Nat → Option Nat) (a b : NumberedWindowLexicalAlgorithm.Requirement) :
    NumberedWindowLexicalAlgorithm.holds C (NumberedWindowLexicalAlgorithm.join a b) = (NumberedWindowLexicalAlgorithm.holds C a && NumberedWindowLexicalAlgorithm.holds C b) := by
  simp [NumberedWindowLexicalAlgorithm.holds,NumberedWindowLexicalAlgorithm.join,List.all_append,Bool.and_assoc,Bool.and_left_comm,Bool.and_comm]

private theorem holdsRestrict (C : Nat → Option Nat) (ok : Bool) (r : NumberedWindowLexicalAlgorithm.Requirement) :
    NumberedWindowLexicalAlgorithm.holds C (NumberedWindowLexicalAlgorithm.restrict ok r) = (ok && NumberedWindowLexicalAlgorithm.holds C r) := by
  simp [NumberedWindowLexicalAlgorithm.holds,NumberedWindowLexicalAlgorithm.restrict,Bool.and_assoc]

theorem typingAux : ExactAuxTermTyping := by
  intro ctx dom cod fn arg
  simp [NumberedWindowLexicalAlgorithm.typed,syntaxAux,annotation,requirementsAux,holdsJoin,holdsRestrict,
    Bool.and_assoc,Bool.and_left_comm,Bool.and_comm]

theorem admissionAux : ExactAuxWindowAdmission := by
  intro s ctx dom cod fn arg
  unfold NumberedWindowScalarAlgorithm.admitted
  rw [typingAux]
  simp [-List.contains_eq_mem,NumberedWindowAdmissionAlgorithm.bits,syntaxAux,rawAdmission,NumberedWindowLexicalAlgorithm.typed,
    Bool.and_assoc,Bool.and_left_comm,Bool.and_comm]

end LogicLineages.PersistentMarking.NumberedWindowAuxExchangeLiftTypingProof
