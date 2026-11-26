import LogicLineages.PersistentMarking.NumberedWindowDirectClassAddressTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticClassAddressProof
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAddressAlgorithmChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticPathClassProof
import LogicLineages.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticNodeProof

namespace LogicLineages.PersistentMarking.NumberedWindowDirectClassAddressProof
open Spine NumberedWindowDirectClassAddress NumberedWindowDirectClassAddressTargets
open NumberedWindowArithmeticClassAddress NumberedWindowArithmeticClassAddressProof
open NumberedWindowArithmeticAllContextBits NumberedWindowArithmeticAddressAlgorithmChecks
open NumberedWindowArithmeticPathCheckBits NumberedWindowArithmeticPathCode
open NumberedWindowArithmeticFields NumberedWindowArithmeticFieldsProof NumberedWindowArithmeticNodeProof
open NumberedWindowArithmeticFieldAlgorithmChecks NumberedWindowArithmeticWitnessListCode
open NumberedWindowClassPathWitnessBits
open NumberedWindowArithmeticAddressAlgorithmTargets (address)
open NumberedWindowFieldAlgorithm (pack packNode)

private theorem decodeSingleton (target certificate : Nat) :
    decodeClassPath (singleHop target certificate) =
      (decodeClassEdge certificate).map (fun edge => [⟨target,edge⟩]) := by
  have fields : decodeFields (pack [packNode 2 [target,certificate]]) =
      some [packNode 2 [target,certificate]] := by
    rw [← exact_ExactOrderedFieldCodec.1]
    exact fieldsRound _
  have node : decodeNode (packNode 2 [target,certificate]) = some (2,[target,certificate]) := by
    rw [← exact_ExactTaggedNodeCodec.1]
    exact nodeRound _ _
  rw [singleHop,decodeClassPath,decodeListOf,fields]
  simp only [Option.bind_eq_bind,Option.bind_some,decodeElements,decodeClassHop,node,
    assembleClassHop,Option.pure_def]
  cases decodeClassEdge certificate <;> rfl

private theorem oneHop (S : Signature) (K Γ : List Ty) (τ : Ty)
    (source certificate target : Nat) :
    positiveClassPathCodeBit S K Γ τ source (singleHop target certificate) target =
      classEdgeCodeBit S K Γ τ source certificate target := by
  rw [positiveClassPathCodeBit,decodeSingleton,classEdgeCodeBit]
  cases decodeClassEdge certificate <;> simp [positiveClassPathBit,classWalkBit]

theorem direct : ExactDirectAddressBit := by
  intro S K positive calibrated
  subst positive
  funext source certificate target
  rw [directAddress,exact_ExactAddressView target]
  cases hd : decodeAddress target with
  | none =>
    cases hs : decodeAddress source <;> simp [literalDirect,hs,hd]
  | some b =>
    cases hs : decodeAddress source with
    | none => simp [literalDirect,addressRSBit,hs,hd]
    | some a =>
      simp only [Option.map_some,Option.any,address,addressRSBit,hs,hd,literalDirect,oneHop]

theorem relation : ExactDirectClassAddress := by
  intro S K hk src dst
  constructor
  · rintro ⟨c,h⟩
    cases hs : decodeAddress src with
    | none => simp [literalDirect,hs] at h
    | some a =>
      cases hd : decodeAddress dst with
      | none => simp [literalDirect,hs,hd] at h
      | some b =>
        rcases a with ⟨Γ,τ,i⟩
        rcases b with ⟨Δ,σ,j⟩
        simp only [literalDirect,hs,hd,Bool.and_eq_true,decide_eq_true_eq] at h
        have sameContext : Γ = Δ := h.1.1
        have sameType : τ = σ := h.1.2
        subst Δ
        subst σ
        obtain ⟨q,r,hq,hr,edge⟩ :=
          (NumberedWindowArithmeticPathClassProof.edge S K Γ τ i j hk).mp ⟨c,h.2⟩
        exact ⟨Γ,τ,i,j,q,r,read hs,read hd,hq,hr,edge⟩
  · rintro ⟨Γ,τ,i,j,q,r,hs,hd,hq,hr,edge⟩
    obtain ⟨c,success⟩ :=
      (NumberedWindowArithmeticPathClassProof.edge S K Γ τ i j hk).mpr ⟨q,r,hq,hr,edge⟩
    refine ⟨c,?_⟩
    simpa only [literalDirect,atCode hs,atCode hd,decide_true,Bool.true_and] using success

end LogicLineages.PersistentMarking.NumberedWindowDirectClassAddressProof
