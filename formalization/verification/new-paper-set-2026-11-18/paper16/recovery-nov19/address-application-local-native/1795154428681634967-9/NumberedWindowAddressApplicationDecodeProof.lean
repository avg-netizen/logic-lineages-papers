import LogicLineages.PersistentMarking.NumberedWindowAddressApplicationTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticScalarChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAddressAlgorithmChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticClassAddressProof

namespace LogicLineages.PersistentMarking.NumberedWindowAddressApplicationDecodeProof
open NumberedWindowAddressApplication NumberedWindowAddressApplicationTargets
open NumberedWindowArithmeticScalarTargets NumberedWindowArithmeticScalarChecks
open NumberedWindowArithmeticClassAddress NumberedWindowArithmeticClassAddressProof
open NumberedWindowArithmeticAddressAlgorithmTargets (address)
open NumberedWindowArithmeticAddressAlgorithmChecks NumberedWindowArithmeticFieldAlgorithmChecks
open NumberedWindowArithmeticAtomCodeChecks NumberedWindowArithmeticTermCodeChecks
open NumberedWindowArithmeticTyCode NumberedWindowArithmeticBinderCode NumberedWindowArithmeticTermCode
open NumberedWindowArithmeticAllContextBits NumberedWindowArithmeticCodecLaws

private theorem typeInject : Function.Injective encodeTy := by
  intro s t he
  have read := exact_TyCodec.2.1 s
  rw [he,exact_TyCodec.2.1 t] at read
  exact (Option.some.inj read).symm

private theorem typeEq (s t : Ty) : (encodeTy s == encodeTy t) = decide (s = t) := by
  apply Bool.eq_iff_iff.mpr
  simp [typeInject.eq_iff]

private theorem contextEq (Γ Δ : List Ty) :
    (Γ.map encodeTy == Δ.map encodeTy) = decide (Γ = Δ) := by
  apply Bool.eq_iff_iff.mpr
  simp [List.map_inj_right (fun _ _ h => typeInject h)]

private theorem arrow (s t : Ty) :
    arrowView (encodeTy (.arrow s t)) = some (encodeTy s,encodeTy t) := by
  simp [encodeTy,arrowView,← NumberedWindowActualPairAlgorithmChecks.currentDecoder,pairRound]

private theorem binders (Γ : List Ty) :
    NumberedWindowFieldAlgorithm.pack (Γ.map encodeTy) = encodeBinders Γ := by
  induction Γ with
  | nil => rfl
  | cons t Γ ih =>
    simp [NumberedWindowFieldAlgorithm.pack,encodeBinders,ih,NumberedWindowActualPairAlgorithmChecks.currentPair]

private theorem packAddress (Γ : List Ty) (τ : Ty) (k : Nat) :
    NumberedWindowFieldAlgorithm.packNode 3 [NumberedWindowFieldAlgorithm.pack (Γ.map encodeTy),encodeTy τ,k] =
      encodeAddress ⟨Γ,τ,k⟩ := by
  rw [encodeAddress,exact_ExactTaggedNodeCodec.1,binders]

private theorem canonicalView (S : Spine.Signature) (K : List Ty) (a : ClassAddress) :
    NumberedWindowScalarAlgorithm.canonical (fixed S K) (address a) = canonicalBit S K a := by
  have h := congrFun (exact_ScalarAddress S K) (encodeAddress a)
  simpa [NumberedWindowScalarAlgorithm.scalar, exact_ExactAddressView (encodeAddress a), round, addressBit] using h

theorem decoded : ExactDecodedApplication := by
  intro S K source argument
  unfold application decodedApplication
  rw [exact_ExactAddressView source,exact_ExactAddressView argument]
  cases decodeAddress source with
  | none => rfl
  | some q =>
    cases decodeAddress argument with
    | none => rfl
    | some u =>
      rcases q with ⟨Γ,ft,i⟩
      rcases u with ⟨Δ,ty,j⟩
      cases ft with
      | ground => rfl
      | arrow σ τ =>
        have canonQ : NumberedWindowScalarAlgorithm.canonical (fixed S K)
            (Γ.map encodeTy,encodeTy (.arrow σ τ),i) =
              canonicalBit S K ⟨Γ,.arrow σ τ,i⟩ := canonicalView S K ⟨Γ,.arrow σ τ,i⟩
        have canonU : NumberedWindowScalarAlgorithm.canonical (fixed S K)
            (Δ.map encodeTy,encodeTy ty,j) =
              canonicalBit S K ⟨Δ,ty,j⟩ := canonicalView S K ⟨Δ,ty,j⟩
        simp only [Option.map_some,Option.bind_eq_bind,Option.bind_some,applyAddresses,
          address,arrow,typeEq,contextEq,canonQ,canonU]
        by_cases valid : (canonicalBit S K ⟨Γ,.arrow σ τ,i⟩ && canonicalBit S K ⟨Δ,ty,j⟩ &&
            decide (Γ = Δ) && decide (σ = ty)) = true
        · simp only [valid,if_true]
          have flags := valid
          simp only [Bool.and_eq_true,decide_eq_true_eq] at flags
          have qGood : canonicalBit S K ⟨Γ,.arrow σ τ,i⟩ = true := flags.1.1.1
          have uGood : canonicalBit S K ⟨Δ,ty,j⟩ = true := flags.1.1.2
          cases hq : decodeTerm i with
          | none => simp [canonicalBit,hq] at qGood
          | some Q =>
            cases hu : decodeTerm j with
            | none => simp [canonicalBit,hu] at uGood
            | some U =>
              have codeQ := (exact_TermCodec.1 i Q).mp hq
              have codeU := (exact_TermCodec.1 j U).mp hu
              have termCode : encodeTerm (.auxApp σ τ Q U) =
                  NumberedWindowFieldAlgorithm.packNode 6 [encodeTy σ,encodeTy τ,i,j] := by
                rw [encodeTerm,exact_ExactTaggedNodeCodec.1,codeQ,codeU]
              rw [← termCode,exact_LeastRepresentative,exact_TermCodec.2.1]
              simp [packAddress]
        · simp [valid]

end LogicLineages.PersistentMarking.NumberedWindowAddressApplicationDecodeProof
