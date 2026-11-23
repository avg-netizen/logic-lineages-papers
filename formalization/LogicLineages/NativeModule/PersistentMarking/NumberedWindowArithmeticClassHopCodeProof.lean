module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticRawHopCodeProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticClassHopCodeProof
open NumberedWindowClassPathWitnessBits
open NumberedWindowArithmeticFields NumberedWindowArithmeticNodeProof
open NumberedWindowArithmeticPathCode NumberedWindowArithmeticRawHopCodeProof

private theorem assembleEdgeSound (tag : Nat) (fields : List Nat) (e : ClassEdgeWitness)
    (h : assembleClassEdge tag fields = some e) :
    encodeClassEdge e = encodeNode tag fields := by
  unfold assembleClassEdge at h
  split at h
  · simp only [Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at h
    obtain ⟨Q,hQ,R,hR,w,hw,rfl⟩ := h
    simp only [encodeClassEdge,termRead hQ,termRead hR,witnessRead hw]
  · cases h

theorem edgeRead (code : Nat) (e : ClassEdgeWitness) (h : decodeClassEdge code = some e) :
    encodeClassEdge e = code :=
  taggedSound encodeClassEdge assembleClassEdge assembleEdgeSound code e h

theorem edgeRound (e : ClassEdgeWitness) : decodeClassEdge (encodeClassEdge e) = some e := by
  cases e with
  | mk Q R w =>
    simp [decodeClassEdge,encodeClassEdge,nodeRound,assembleClassEdge,
      NumberedWindowArithmeticTermCodeComplete.termRound,
      NumberedWindowArithmeticRawWitnessCodeComplete.roundtrip]

private theorem assembleHopSound (tag : Nat) (fields : List Nat) (e : ClassHop)
    (h : assembleClassHop tag fields = some e) : encodeClassHop e = encodeNode tag fields := by
  unfold assembleClassHop at h
  split at h
  · obtain ⟨edge,he,rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [encodeClassHop,edgeRead _ _ he]
  · cases h

theorem hopRead (code : Nat) (e : ClassHop) (h : decodeClassHop code = some e) :
    encodeClassHop e = code :=
  taggedSound encodeClassHop assembleClassHop assembleHopSound code e h

theorem hopRound (e : ClassHop) : decodeClassHop (encodeClassHop e) = some e := by
  cases e
  simp [decodeClassHop,encodeClassHop,nodeRound,assembleClassHop,edgeRound]

end LogicLineages.PersistentMarking.NumberedWindowArithmeticClassHopCodeProof
