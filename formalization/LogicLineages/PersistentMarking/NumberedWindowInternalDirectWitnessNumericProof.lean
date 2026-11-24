module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectWitnessEnvelopeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserNumericChecks

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectWitnessNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalSparsePathEnvelope (run field cursor applyUnary)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (nodeArity applyValue)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
  (headTailOfCell noNode nodeOfCell codeOfCell packOfUnpack cellAt)
open NumberedWindowInternalSparseFieldCell (chosenCell cellHead cellTail)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (literalEvaluation)
open NumberedWindowInternalDirectWitnessEnvelopeTargets
open NumberedWindowInternalSparseFieldParserNumericChecks (exact_ActualDecodedOutput)
open NumberedWindowFieldAlgorithm (pack unpack unpackNode)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowDirectAlgorithm (readEntry readWitness entries)

theorem exact_TripleGuard (tag n : Nat) :
    run (guardAt tag) n = 1 ↔ ∃ a b c, unpackNode n = some (tag,[a,b,c]) := by
  have value : run (literal 1 tag) n = tag := literalEvaluation 1 tag (n ::ᵥ nil)
  unfold guardAt
  rw [nodeArity (literal 1 tag) 3 n tag value]
  constructor
  · rintro ⟨ls,ok,size⟩
    rcases ls with _ | ⟨a,_ | ⟨b,_ | ⟨c,_ | ⟨d,rest⟩⟩⟩⟩ <;> simp at size
    exact ⟨a,b,c,ok⟩
  · rintro ⟨a,b,c,ok⟩
    exact ⟨[a,b,c],ok,rfl⟩

private theorem nodeCode {n tag : Nat} {xs : List Nat} (h : unpackNode n = some (tag,xs)) :
    n = pair tag (pack xs) + 1 := by
  cases found : chosenCell n with
  | none => rw [noNode found] at h; cases h
  | some both =>
    obtain ⟨head,tail⟩ := both
    rw [nodeOfCell found] at h
    cases parsed : unpack tail with
    | none => rw [parsed] at h; cases h
    | some fs =>
      rw [parsed] at h
      have e : (head,fs) = (tag,xs) := Option.some.inj h
      have h₁ : head = tag := congrArg Prod.fst e
      have h₂ : fs = xs := congrArg Prod.snd e
      rw [codeOfCell found,h₁,packOfUnpack tail parsed,h₂]

theorem exact_TripleFields {tag n a b c : Nat} (h : unpackNode n = some (tag,[a,b,c])) :
    run (field 0) n = a ∧ run (field 1) n = b ∧ run (field 2) n = c := by
  rw [nodeCode h]
  have outer := (headTailOfCell (cellAt tag (pack [a,b,c]))).2
  have first : run cellHead (pack [a,b,c]) = a ∧ run cellTail (pack [a,b,c]) = pack [b,c] :=
    headTailOfCell (cellAt a (pack [b,c]))
  have second : run cellHead (pack [b,c]) = b ∧ run cellTail (pack [b,c]) = pack [c] :=
    headTailOfCell (cellAt b (pack [c]))
  have third : run cellHead (pack [c]) = c := (headTailOfCell (cellAt c (pack []))).1
  exact ⟨by simp only [field,cursor,applyValue,outer,first.1],
    by simp only [field,cursor,applyValue,outer,first.2,second.1],
    by simp only [field,cursor,applyValue,outer,first.2,second.2,third]⟩

theorem exact_DirectRawTriple : ExactRawTriple := by
  intro tag n
  by_cases h : run (guardAt tag) n = 1
  · obtain ⟨a,b,c,ok⟩ := (exact_TripleGuard tag n).mp h
    obtain ⟨p,q,r⟩ := exact_TripleFields ok
    simp [rawTriple,h,ok,p,q,r]
  · unfold rawTriple
    rw [if_neg h]
    cases got : unpackNode n with
    | none => rfl
    | some p =>
      obtain ⟨t,fs⟩ := p
      rcases fs with _ | ⟨a,_ | ⟨b,_ | ⟨c,_ | ⟨d,rest⟩⟩⟩⟩ <;> try rfl
      have miss : t ≠ tag := by
        intro eq
        subst t
        exact h ((exact_TripleGuard tag n).mpr ⟨a,b,c,got⟩)
      exact (if_neg miss).symm

theorem exact_DirectSelectedEntry (raw : Nat) : rawTriple 4 raw = readEntry raw := by
  rw [exact_DirectRawTriple 4 raw]
  unfold readEntry
  cases unpackNode raw with
  | none => rfl
  | some p =>
    obtain ⟨tag,ls⟩ := p
    rcases tag with _ | _ | _ | _ | _ | n <;>
      rcases ls with _ | ⟨a,_ | ⟨b,_ | ⟨c,_ | ⟨d,rest⟩⟩⟩⟩ <;> rfl

theorem exact_DirectSelectedEntries (rs : List Nat) : selectedEntries rs = entries rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [selectedEntries,entries,exact_DirectSelectedEntry,ih]

theorem exact_DirectSelectedWitness : ExactSelectedWitness := by
  intro n
  unfold selectedWitness readWitness
  rw [exact_DirectRawTriple 5 n]
  cases unpackNode n with
  | none => rfl
  | some p =>
    obtain ⟨tag,ls⟩ := p
    rcases tag with _ | _ | _ | _ | _ | _ | t <;>
      rcases ls with _ | ⟨a,_ | ⟨b,_ | ⟨c,_ | ⟨d,rest⟩⟩⟩⟩ <;> try rfl
    change (do
      let kept ← selectedList a
      let removed ← selectedList b
      let raw ← selectedList c
      let added ← selectedEntries raw
      pure (kept,removed,added)) = (do
      let kept ← unpack a
      let removed ← unpack b
      let raw ← unpack c
      let added ← entries raw
      pure (kept,removed,added))
    have picked (v : Nat) : selectedList v = unpack v := exact_ActualDecodedOutput v
    simp only [picked,exact_DirectSelectedEntries]

#print axioms exact_TripleGuard
#print axioms exact_TripleFields
#print axioms exact_DirectRawTriple
#print axioms exact_DirectSelectedEntry
#print axioms exact_DirectSelectedEntries
#print axioms exact_DirectSelectedWitness
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectWitnessNumericProof
