import LogicLineages.PersistentMarking.NumberedWindowPositivePathTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmChecks

namespace LogicLineages.PersistentMarking.NumberedWindowPositivePathParsingProof
open NumberedWindowPositivePathAlgorithm
open NumberedWindowArithmeticPathCode NumberedWindowArithmeticFields
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticRawWitnessCode
open NumberedWindowClassPathWitnessBits (ClassEdgeWitness)
open NumberedWindowArithmeticFieldAlgorithmChecks (exact_ExactTaggedNodeCodec)

def edgePayload (row : RawEdge) : Option ClassEdgeWitness := do
  let q ← decodeTerm row.1
  let r ← decodeTerm row.2.2
  let w ← decodeWitness row.2.1
  pure ⟨q,r,w⟩

theorem edgeParsed (n : Nat) : decodeClassEdge n = (edgeView n).bind edgePayload := by
  unfold decodeClassEdge edgeView
  rw [← exact_ExactTaggedNodeCodec.2]
  rcases decodeNode n with _ | ⟨tag,fs⟩
  · rfl
  · rcases tag with _ | _ | tag <;>
      rcases fs with _ | ⟨q,_ | ⟨r,_ | ⟨w,_ | ⟨x,rest⟩⟩⟩⟩ <;> rfl

def hopPayload (row : ClassHop) : Option NumberedWindowClassPathWitnessBits.ClassHop :=
  (edgePayload row.2).map (NumberedWindowClassPathWitnessBits.ClassHop.mk row.1)

theorem hopParsed (n : Nat) : decodeClassHop n = (hopView n).bind hopPayload := by
  unfold decodeClassHop hopView
  rw [← exact_ExactTaggedNodeCodec.2]
  rcases decodeNode n with _ | ⟨tag,fs⟩
  · rfl
  · rcases tag with _ | _ | _ | tag <;>
      rcases fs with _ | ⟨t,_ | ⟨e,_ | ⟨x,rest⟩⟩⟩
    all_goals try rfl
    change (decodeClassEdge e).map (NumberedWindowClassPathWitnessBits.ClassHop.mk t) =
      (do let row ← edgeView e; pure (t,row)).bind hopPayload
    rw [edgeParsed]
    cases edgeView e <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowPositivePathParsingProof
