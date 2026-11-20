module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeSelectorEvaluationProof
open NumberedWindowInternalSparseFieldCell (chosenCell cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelope
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowFieldAlgorithm (pack unpack unpackNode)
open NumberedWindowPositivePathAlgorithm (edgeView hopView)

private theorem nodeCode {n k : Nat} {xs : List Nat}
    (found : unpackNode n = some (k,xs)) :
    n = pair k (pack xs) + 1 := by
  cases hit : chosenCell n with
  | none => rw [noNode hit] at found; cases found
  | some both =>
    obtain ⟨h,t⟩ := both
    rw [nodeOfCell hit] at found
    cases got : unpack t with
    | none => cases found
    | some fs =>
      have eq : (h,fs) = (k,xs) := Option.some.inj found
      have tag := congrArg Prod.fst eq
      have fields := congrArg Prod.snd eq
      have body := packOfUnpack t got
      rw [codeOfCell hit, tag, body, fields]

theorem edgeProjections {n q r w : Nat} (found : unpackNode n = some (1,[q,r,w])) :
    run edgeSource n = q ∧ run edgeWitness n = w ∧ run edgeTarget n = r := by
  rw [nodeCode found]
  have outer := (headTailOfCell (cellAt 1 (pack [q,r,w]))).2
  have first : run cellHead (pack [q,r,w]) = q ∧ run cellTail (pack [q,r,w]) = pack [r,w] :=
    headTailOfCell (cellAt q (pack [r,w]))
  have second : run cellHead (pack [r,w]) = r ∧ run cellTail (pack [r,w]) = pack [w] :=
    headTailOfCell (cellAt r (pack [w]))
  have third : run cellHead (pack [w]) = w :=
    (headTailOfCell (cellAt w (pack []))).1
  exact ⟨by simp only [edgeSource,field,cursor,applyValue,outer,first.1],
    by simp only [edgeWitness,field,cursor,applyValue,outer,first.2,second.2,third],
    by simp only [edgeTarget,field,cursor,applyValue,outer,first.2,second.1]⟩

theorem hopProjections {n t e : Nat} (found : unpackNode n = some (2,[t,e])) :
    run hopTarget n = t ∧ run (field 1) n = e := by
  rw [nodeCode found]
  have outer := (headTailOfCell (cellAt 2 (pack [t,e]))).2
  have first : run cellHead (pack [t,e]) = t ∧ run cellTail (pack [t,e]) = pack [e] :=
    headTailOfCell (cellAt t (pack [e]))
  have second : run cellHead (pack [e]) = e :=
    (headTailOfCell (cellAt e (pack []))).1
  exact ⟨by simp only [hopTarget,field,cursor,applyValue,outer,first.1],
    by simp only [field,cursor,applyValue,outer,first.2,second]⟩

theorem edgeViewSome {n q w r : Nat} :
    edgeView n = some (q,w,r) ↔ unpackNode n = some (1,[q,r,w]) := by
  unfold edgeView
  cases found : unpackNode n with
  | none => simp
  | some both =>
    obtain ⟨tag,fs⟩ := both
    rcases tag with _ | _ | tag <;>
      rcases fs with _ | ⟨a,_ | ⟨b,_ | ⟨c,_ | ⟨d,rest⟩⟩⟩⟩ <;>
      simp [and_assoc,and_comm,and_left_comm]

theorem hopOutside {n : Nat} (absent : ¬ ∃ t e, unpackNode n = some (2,[t,e])) :
    hopView n = none := by
  unfold hopView
  cases found : unpackNode n with
  | none => rfl
  | some both =>
    rcases both with ⟨tag,fs⟩
    rcases tag with _ | _ | _ | tag <;>
      rcases fs with _ | ⟨a,_ | ⟨b,_ | ⟨c,rest⟩⟩⟩ <;> try rfl
    exact False.elim (absent ⟨a,b,found⟩)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeSelectorEvaluationProof
