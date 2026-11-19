import LogicLineages.PersistentMarking.NumberedWindowArithmeticPathCodeTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticRawWitnessCodeChecks

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticRawHopCodeProof
open NumberedWindowSyntax NumberedWindowRawWitnessBits NumberedWindowPathWitnessBits
open NumberedWindowArithmeticFields NumberedWindowArithmeticNodeProof
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticRawWitnessCode
open NumberedWindowArithmeticPathCode
universe u

theorem termRead {code : Nat} {Q : NTerm} (h : decodeTerm code = some Q) :
    encodeTerm Q = code :=
  (NumberedWindowArithmeticTermCodeSound.atFuel code).1 code Q h

theorem witnessRead {code : Nat} {w : RawWitness} (h : decodeWitness code = some w) :
    encodeWitness w = code :=
  NumberedWindowArithmeticRawWitnessCodeSound.atFuel code code w h

theorem taggedSound {α : Type u} (enc : α → Nat) (assemble : Nat → List Nat → Option α)
    (hs : ∀ tag fields v, assemble tag fields = some v → enc v = encodeNode tag fields)
    (code : Nat) (v : α)
    (h : (decodeNode code).bind (fun p => assemble p.1 p.2) = some v) :
    enc v = code := by
  obtain ⟨p,hp,hv⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tag,fields⟩ := p
  exact (hs tag fields v hv).trans (nodeRead hp)

private theorem assembleSound (tag : Nat) (fields : List Nat) (e : RawHop)
    (h : assembleRawHop tag fields = some e) : encodeRawHop e = encodeNode tag fields := by
  unfold assembleRawHop at h
  split at h
  · simp only [Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at h
    obtain ⟨Q,hQ,w,hw,rfl⟩ := h
    simp only [encodeRawHop,termRead hQ,witnessRead hw]
  · cases h

theorem rawRead (code : Nat) (e : RawHop) (h : decodeRawHop code = some e) :
    encodeRawHop e = code :=
  taggedSound encodeRawHop assembleRawHop assembleSound code e h

theorem rawRound (e : RawHop) : decodeRawHop (encodeRawHop e) = some e := by
  cases e with
  | mk Q w =>
    simp [decodeRawHop,encodeRawHop,nodeRound,assembleRawHop,
      NumberedWindowArithmeticTermCodeComplete.termRound,
      NumberedWindowArithmeticRawWitnessCodeComplete.roundtrip]

end LogicLineages.PersistentMarking.NumberedWindowArithmeticRawHopCodeProof
