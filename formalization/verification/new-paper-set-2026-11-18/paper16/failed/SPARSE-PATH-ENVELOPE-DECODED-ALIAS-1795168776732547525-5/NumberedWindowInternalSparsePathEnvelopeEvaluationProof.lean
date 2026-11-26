module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeSelectorEvaluationProof
import Mathlib.Data.List.Basic

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeEvaluationProof
open NumberedWindowInternalSparsePathEnvelope
open NumberedWindowInternalSparsePathEnvelopeTargets
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
open NumberedWindowInternalSparsePathEnvelopeSelectorEvaluationProof
open NumberedWindowPositivePathAlgorithm (edgeView hopView)
open NumberedWindowFieldAlgorithm (unpackNode)

theorem acceptedEdge (n : Nat) :
    run edgeGood n = 1 ↔ ∃ q r w, unpackNode n = some (1,[q,r,w]) := by
  rw [edgeGood,nodeArity one 3 n 1 (oneValue n)]
  constructor
  · rintro ⟨xs,found,length⟩
    obtain ⟨q,r,w,rfl⟩ := List.length_eq_three.mp length
    exact ⟨q,r,w,found⟩
  · rintro ⟨q,r,w,found⟩
    exact ⟨[q,r,w],found,rfl⟩

theorem acceptedOuterHop (n : Nat) :
    run (nodeGood two 2) n = 1 ↔ ∃ t e, unpackNode n = some (2,[t,e]) := by
  rw [nodeArity two 2 n 2 (twoValue n)]
  constructor
  · rintro ⟨xs,found,length⟩
    obtain ⟨t,e,rfl⟩ := List.length_eq_two.mp length
    exact ⟨t,e,found⟩
  · rintro ⟨t,e,found⟩
    exact ⟨[t,e],found,rfl⟩

theorem edge : AllInputEdgeEnvelope := by
  intro n
  cases out : edgeView n with
  | none =>
    have notGood : run edgeGood n ≠ 1 := by
      intro good
      obtain ⟨q,r,w,found⟩ := (acceptedEdge n).mp good
      have e : edgeView n = some (q,w,r) := edgeViewSome.mpr found
      rw [out] at e
      cases e
    rw [selectedEdge, if_neg notGood]
  | some out =>
    obtain ⟨q,w,r⟩ := out
    have found := edgeViewSome.mp out
    have good := (acceptedEdge n).mpr ⟨q,r,w,found⟩
    obtain ⟨hq,hw,hr⟩ := edgeProjections found
    rw [selectedEdge,if_pos good,hq,hw,hr]

theorem hop : AllInputHopEnvelope := by
  intro n
  by_cases outer : run (nodeGood two 2) n = 1
  · obtain ⟨t,e,found⟩ := (acceptedOuterHop n).mp outer
    obtain ⟨ht,he⟩ := hopProjections found
    have form : hopView n = (edgeView e).map (fun x => (t,x)) := by
      unfold hopView
      rw [found]
      cases edgeView e <;> rfl
    rw [form,← edge e]
    have guard : run hopGood n = 1 ↔ run edgeGood e = 1 := by
      rw [hopGood,bothAccept,applyValue,he]
      exact ⟨And.right,fun h => ⟨outer,h⟩⟩
    by_cases accepts : run edgeGood e = 1
    · simp only [selectedHop,guard,if_pos accepts,selectedEdge,ht,hopSource,
        hopWitness,hopRawTarget,applyValue,he,Option.map_some]
    · simp only [selectedHop,guard,if_neg accepts,selectedEdge,Option.map_none]
  · have guard : run hopGood n ≠ 1 := by
      intro accepted
      rw [hopGood,bothAccept] at accepted
      exact outer accepted.1
    rw [selectedHop,if_neg guard,hopOutside (fun h => outer ((acceptedOuterHop n).mpr h))]

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeEvaluationProof
