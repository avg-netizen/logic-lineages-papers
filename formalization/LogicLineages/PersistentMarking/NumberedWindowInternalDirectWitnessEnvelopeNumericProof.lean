module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectWitnessEnvelopeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserNumericChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectWitnessEnvelope
open NumberedWindowInternalDirectWitnessEnvelopeTargets
open NumberedWindowInternalSparsePathEnvelope
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (applyValue nodeArity)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (cellAt headTailOfCell codeOfCell noNode nodeOfCell packOfUnpack)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail chosenCell)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (literalEvaluation)
open NumberedWindowInternalSparseFieldParserNumericChecks (exact_ActualDecodedOutput)
open NumberedWindowFieldAlgorithm (pack packNode unpackNode unpack)
open NumberedWindowDirectAlgorithm (readEntry entries readWitness Entry)

private theorem guardSpec (tag n : Nat) :
    run (guardAt tag) n = 1 ↔ ∃ a b c, unpackNode n = some (tag,[a,b,c]) := by
  have hv : run (NumberedWindowInternalFreshProbeDispatchProgram.literal 1 tag) n = tag :=
    literalEvaluation 1 tag _
  change run (nodeGood (NumberedWindowInternalFreshProbeDispatchProgram.literal 1 tag) 3) n = 1 ↔ _
  rw [nodeArity _ _ _ _ hv]
  constructor
  · rintro ⟨xs,hx,hl⟩
    rcases xs with _ | ⟨a,_ | ⟨b,_ | ⟨c,_ | ⟨d,rest⟩⟩⟩⟩ <;>
      first | exact ⟨a,b,c,hx⟩ | simp at hl
  · rintro ⟨a,b,c,h⟩
    exact ⟨[a,b,c],h,rfl⟩

private theorem rawNodeCode {n tag : Nat} {fs : List Nat}
    (found : unpackNode n = some (tag,fs)) :
    n = packNode tag fs := by
  cases cell : chosenCell n with
  | none => rw [noNode cell] at found; cases found
  | some p =>
    obtain ⟨k,t⟩ := p
    rw [nodeOfCell cell] at found
    cases h : unpack t with
    | none => rw [h] at found; cases found
    | some actual =>
      rw [h] at found
      have e : (k,actual) = (tag,fs) := Option.some.inj found
      have hk : k = tag := congrArg Prod.fst e
      have hf : actual = fs := congrArg Prod.snd e
      rw [codeOfCell cell,hk,packOfUnpack t h,hf] <;> rfl

private theorem numericReports (tag n a b c : Nat)
    (h : unpackNode n = some (tag,[a,b,c])) :
    run (field 0) n = a ∧ run (field 1) n = b ∧ run (field 2) n = c := by
  rw [rawNodeCode h]
  have tail := (headTailOfCell (cellAt tag (pack [a,b,c]))).2
  have aPair : run cellHead (pack [a,b,c]) = a ∧ run cellTail (pack [a,b,c]) = pack [b,c] :=
    headTailOfCell (cellAt a (pack [b,c]))
  have bPair : run cellHead (pack [b,c]) = b ∧ run cellTail (pack [b,c]) = pack [c] :=
    headTailOfCell (cellAt b (pack [c]))
  have cHead : run cellHead (pack [c]) = c := (headTailOfCell (cellAt c (pack []))).1
  change run (field 0) (NumberedWindowPairAlgorithm.pair tag (pack [a,b,c]) + 1) = a ∧
    run (field 1) (NumberedWindowPairAlgorithm.pair tag (pack [a,b,c]) + 1) = b ∧
    run (field 2) (NumberedWindowPairAlgorithm.pair tag (pack [a,b,c]) + 1) = c
  exact ⟨by simp only [field,cursor,applyValue,tail,aPair.1],
    by simp only [field,cursor,applyValue,tail,aPair.2,bPair.1],
    by simp only [field,cursor,applyValue,tail,aPair.2,bPair.2,cHead]⟩

theorem exactRawTriple : ExactRawTriple := by
  intro tag n
  unfold rawTriple
  by_cases good : run (guardAt tag) n = 1
  · obtain ⟨a,b,c,h⟩ := (guardSpec tag n).mp good
    obtain ⟨ha,hb,hc⟩ := numericReports tag n a b c h
    rw [if_pos good,h,ha,hb,hc] <;> simp
  · have no : ¬ ∃ a b c, unpackNode n = some (tag,[a,b,c]) :=
      fun h => good ((guardSpec tag n).mpr h)
    rw [if_neg good]
    cases h : unpackNode n with
    | none => rfl
    | some p =>
      obtain ⟨k,xs⟩ := p
      rcases xs with _ | ⟨a,_ | ⟨b,_ | ⟨c,_ | ⟨d,rest⟩⟩⟩⟩ <;> try rfl
      have ne : k ≠ tag := by
        intro eq
        subst k
        exact no ⟨a,b,c,h⟩
      simp [ne]

private theorem exactEntry (n : Nat) : rawTriple 4 n = readEntry n := by
  rw [exactRawTriple]
  unfold readEntry
  cases h : unpackNode n with
  | none => rfl
  | some p =>
    obtain ⟨tag,xs⟩ := p
    rcases xs with _ | ⟨a,_ | ⟨b,_ | ⟨c,_ | ⟨d,rest⟩⟩⟩⟩ <;>
      rcases tag with _ | _ | _ | _ | _ | tag <;> rfl

private theorem exactEntries (xs : List Nat) : selectedEntries xs = entries xs := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [selectedEntries,entries,exactEntry,ih]

theorem exactSelectedWitness : ExactSelectedWitness := by
  intro n
  unfold selectedWitness
  rw [exactRawTriple]
  simp only [exactEntries]
  unfold readWitness
  cases h : unpackNode n with
  | none => rfl
  | some p =>
    obtain ⟨tag,xs⟩ := p
    rcases xs with _ | ⟨a,_ | ⟨b,_ | ⟨c,_ | ⟨d,rest⟩⟩⟩⟩ <;>
      rcases tag with _ | _ | _ | _ | _ | _ | tag <;> try rfl
    change (do
      let kept ← selectedList a
      let removed ← selectedList b
      let raw ← selectedList c
      let added ← entries raw
      pure (kept,removed,added)) = (do
        let kept ← unpack a
        let removed ← unpack b
        let raw ← unpack c
        let added ← entries raw
        pure (kept,removed,added))
    have selectedExact (v : Nat) : selectedList v = unpack v := exact_ActualDecodedOutput v
    simp only [selectedExact]

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectWitnessEnvelope
