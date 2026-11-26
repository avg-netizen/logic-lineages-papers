module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPositivePathParsingProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticAddressAlgorithmChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticAtomCodeChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPositivePathProof
open NumberedWindowPositivePathAlgorithm NumberedWindowPositivePathTargets
open NumberedWindowPositivePathParsingProof
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticRawWitnessCode
open NumberedWindowArithmeticTyCode NumberedWindowArithmeticPathCode
open NumberedWindowArithmeticPathCheckBits NumberedWindowArithmeticAllContextBits
open NumberedWindowArithmeticClassAddress (decodeAddress)
open NumberedWindowArithmeticWitnessListCode
open NumberedWindowClassPathWitnessBits (classEdgeBit classWalkBit positiveClassPathBit)

private theorem optionCodeEq (a b : Option Nat) : (a == b) = decide (a = b) := by
  apply Bool.eq_iff_iff.mpr
  simp

private theorem advanceExact {S K step least} (h : Callbacks S K step least)
    (Γ : List Ty) (τ : Ty) (source code : Nat) :
    advance (step (Γ.map encodeTy) (encodeTy τ)) (least (Γ.map encodeTy) (encodeTy τ))
      (some source) code =
      (decodeClassHop code).bind (fun hop =>
        if classEdgeBit S K Γ τ source hop.targetCode hop.edge then some hop.targetCode else none) := by
  rw [hopParsed]
  cases hn : hopView code with
  | none => simp [advance,hn]
  | some row =>
    rcases row with ⟨target,q,w,r⟩
    rcases h with ⟨hStep,hLeast⟩
    simp only [advance,hn,Option.bind_some,hStep,hLeast,windowStepCodeBit,optionCodeEq]
    cases hq : decodeTerm q <;> cases hr : decodeTerm r <;> cases hw : decodeWitness w <;>
      simp [hopPayload,edgePayload,between,hq,hr,hw,classEdgeBit]

private theorem failedFold (step : Nat → Nat → Nat → Bool) (least : Nat → Option Nat)
    (codes : List Nat) : codes.foldl (advance step least) none = none := by
  induction codes with
  | nil => rfl
  | cons code codes ih =>
    change codes.foldl (advance step least) none = none
    exact ih

private theorem walkExact {S K step least} (h : Callbacks S K step least)
    (Γ : List Ty) (τ : Ty) (codes : List Nat) (source target : Nat) :
    walk (step (Γ.map encodeTy) (encodeTy τ)) (least (Γ.map encodeTy) (encodeTy τ))
        source codes target =
      (decodeElements decodeClassHop codes).any (fun es => classWalkBit S K Γ τ source es target) := by
  induction codes generalizing source with
  | nil =>
    simp only [walk,List.foldl_nil,decodeElements,classWalkBit,Option.any,optionCodeEq,
      Option.some.injEq]
  | cons code codes ih =>
    unfold walk
    rw [List.foldl_cons,advanceExact h Γ τ]
    cases hn : decodeClassHop code with
    | none =>
      simp [decodeElements,hn,failedFold]
    | some hop =>
      by_cases hb : classEdgeBit S K Γ τ source hop.targetCode hop.edge = true
      · change ((codes.foldl (advance _ _) _) == some target) = _
        simp only [Option.bind_some,hb,if_true]
        have tail := ih hop.targetCode
        unfold walk at tail
        rw [tail]
        cases ht : decodeElements decodeClassHop codes with
        | none => simp [decodeElements,hn,ht]
        | some es => simp [decodeElements,hn,ht,Option.any,classWalkBit,hb]
      · have hf : classEdgeBit S K Γ τ source hop.targetCode hop.edge = false :=
          Bool.eq_false_iff.mpr hb
        cases ht : decodeElements decodeClassHop codes <;>
          simp [decodeElements,hn,ht,hf,failedFold,Option.any,classWalkBit]

theorem positiveExact : ExactPositivePath := by
  intro S K step least h Γ τ source cert target
  unfold positive positiveClassPathCodeBit decodeClassPath decodeListOf
  rw [← NumberedWindowArithmeticFieldAlgorithmChecks.exact_ExactOrderedFieldCodec.2]
  cases hn : NumberedWindowArithmeticFields.decodeFields cert with
  | none => rfl
  | some codes =>
    cases codes with
    | nil => rfl
    | cons code codes =>
      change walk (step (Γ.map encodeTy) (encodeTy τ)) (least (Γ.map encodeTy) (encodeTy τ))
        source (code :: codes) target = _
      rw [walkExact h Γ τ]
      cases hh : decodeClassHop code <;> cases ht : decodeElements decodeClassHop codes <;>
        simp [decodeElements,hh,ht,Option.any,positiveClassPathBit]

private theorem typeCodeInject : Function.Injective encodeTy := by
  intro t u h
  have hr := NumberedWindowArithmeticAtomCodeChecks.exact_TyCodec.2.1 t
  rw [h,NumberedWindowArithmeticAtomCodeChecks.exact_TyCodec.2.1 u] at hr
  exact (Option.some.inj hr).symm

theorem addressExact : ExactAddressRS := by
  intro S K step least h source cert target
  unfold addressRS addressRSBit
  rw [NumberedWindowArithmeticAddressAlgorithmChecks.exact_ExactAddressView source,
    NumberedWindowArithmeticAddressAlgorithmChecks.exact_ExactAddressView target]
  cases decodeAddress source <;> cases decodeAddress target
  all_goals try rfl
  rename_i a b
  simp only [Option.map_some,NumberedWindowArithmeticAddressAlgorithmTargets.address]
  have hc : (a.context.map encodeTy == b.context.map encodeTy) = decide (a.context = b.context) := by
    apply Bool.eq_iff_iff.mpr
    simp [List.map_inj_right (fun _ _ he => typeCodeInject he)]
  have ht : (encodeTy a.result == encodeTy b.result) = decide (a.result = b.result) := by
    apply Bool.eq_iff_iff.mpr
    simp [typeCodeInject.eq_iff]
  rw [hc,ht,positiveExact S K step least h]

end LogicLineages.PersistentMarking.NumberedWindowPositivePathProof
