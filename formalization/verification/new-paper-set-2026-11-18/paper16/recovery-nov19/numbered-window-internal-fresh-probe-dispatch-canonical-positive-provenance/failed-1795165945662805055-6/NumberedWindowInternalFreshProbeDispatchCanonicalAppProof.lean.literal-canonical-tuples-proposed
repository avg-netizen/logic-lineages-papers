import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchCanonicalAppTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticScalarChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAddressAlgorithmChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticClassAddressProof

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchCanonicalAppProof
open NumberedWindowInternalFreshProbeDispatchCanonicalAppTargets
open NumberedWindowAddressApplication NumberedWindowAddressApplicationTargets
open NumberedWindowArithmeticScalarTargets NumberedWindowArithmeticScalarChecks
open NumberedWindowArithmeticClassAddress NumberedWindowArithmeticClassAddressProof
open NumberedWindowArithmeticAddressAlgorithmTargets (address)
open NumberedWindowArithmeticAddressAlgorithmChecks NumberedWindowArithmeticFieldAlgorithmChecks
open NumberedWindowArithmeticTermCodeChecks NumberedWindowArithmeticCodecLaws
open NumberedWindowArithmeticTyCode NumberedWindowArithmeticBinderCode NumberedWindowArithmeticTermCode
open NumberedWindowArithmeticAllContextBits NumberedWindowArithmeticLeastClass
open NumberedWindowAddressAlgorithm (addressView)
open NumberedWindowFieldAlgorithm (pack packNode)

private theorem viewAt (a : ClassAddress) : addressView (encodeAddress a) = some (address a) := by
  rw [exact_ExactAddressView,round]
  rfl

private theorem canonicalAt (S : Spine.Signature) (K : List Ty) (a : ClassAddress) :
    NumberedWindowScalarAlgorithm.canonical (fixed S K) (address a) = canonicalBit S K a := by
  have he := congrFun (exact_ScalarAddress S K) (encodeAddress a)
  simpa only [NumberedWindowScalarAlgorithm.scalar,viewAt,Option.any_some,addressBit,round] using he

private theorem arrowAt (σ τ : Ty) :
    arrowView (encodeTy (.arrow σ τ)) = some (encodeTy σ,encodeTy τ) := by
  simp [encodeTy,arrowView,← NumberedWindowActualPairAlgorithmChecks.currentDecoder,pairRound]

private theorem binderPack (Γ : List Ty) : pack (Γ.map encodeTy) = encodeBinders Γ := by
  induction Γ with
  | nil => rfl
  | cons t Γ ih =>
    simp [pack,encodeBinders,ih,NumberedWindowActualPairAlgorithmChecks.currentPair]

private theorem resultPack (Γ : List Ty) (τ : Ty) (k : Nat) :
    packNode 3 [pack (Γ.map encodeTy),encodeTy τ,k] = encodeAddress ⟨Γ,τ,k⟩ := by
  rw [encodeAddress,exact_ExactTaggedNodeCodec.1,binderPack]

/-- On these literal matching addresses there is no case analysis on a raw
decoder, unknown type, unknown context, or ill-typed application branch. -/
private theorem rawAt (S : Spine.Signature) (K Γ : List Ty) (σ τ : Ty) (i j : Nat)
    (hq : canonicalBit S K ⟨Γ,.arrow σ τ,i⟩ = true)
    (hu : canonicalBit S K ⟨Γ,σ,j⟩ = true) :
    application (fixed S K) (encodeAddress ⟨Γ,.arrow σ τ,i⟩) (encodeAddress ⟨Γ,σ,j⟩) =
      (NumberedWindowScalarAlgorithm.least (fixed S K) (Γ.map encodeTy) (encodeTy τ)
        (packNode 6 [encodeTy σ,encodeTy τ,i,j])).map
        (fun k => packNode 3 [pack (Γ.map encodeTy),encodeTy τ,k]) := by
  have hqc := (canonicalAt S K ⟨Γ,.arrow σ τ,i⟩).trans hq
  have huc := (canonicalAt S K ⟨Γ,σ,j⟩).trans hu
  change NumberedWindowScalarAlgorithm.canonical (fixed S K)
    (Γ.map encodeTy,encodeTy (.arrow σ τ),i) = true at hqc
  change NumberedWindowScalarAlgorithm.canonical (fixed S K)
    (Γ.map encodeTy,encodeTy σ,j) = true at huc
  unfold application
  rw [viewAt,viewAt]
  simp only [Option.bind_eq_bind,Option.bind_some,applyAddresses,arrowAt,address,
    hqc,huc,beq_self_eq_true,Bool.true_and,if_true]

private theorem decodedAt (S : Spine.Signature) (K Γ : List Ty) (σ τ : Ty) (i j : Nat)
    (Q U : NumberedWindowSyntax.NTerm)
    (hq : canonicalBit S K ⟨Γ,.arrow σ τ,i⟩ = true)
    (hu : canonicalBit S K ⟨Γ,σ,j⟩ = true)
    (hQ : decodeTerm i = some Q) (hU : decodeTerm j = some U) :
    decodedApplication S K (encodeAddress ⟨Γ,.arrow σ τ,i⟩) (encodeAddress ⟨Γ,σ,j⟩) =
      (leastCode S K Γ τ (.auxApp σ τ Q U)).map (fun k => encodeAddress ⟨Γ,τ,k⟩) := by
  simp only [decodedApplication,round,Option.bind_eq_bind,Option.bind_some,hq,hu,
    decide_true,Bool.true_and,if_true,hQ,hU]

theorem exact_CanonicalLiteralApplication : ExactCanonicalLiteralApplication := by
  intro S K Γ σ τ i j hq hu
  cases hQ : decodeTerm i with
  | none => simp [canonicalBit,hQ] at hq
  | some Q =>
    cases hU : decodeTerm j with
    | none => simp [canonicalBit,hU] at hu
    | some U =>
      have codeQ := (exact_TermCodec.1 i Q).mp hQ
      have codeU := (exact_TermCodec.1 j U).mp hU
      have termCode : encodeTerm (.auxApp σ τ Q U) =
          packNode 6 [encodeTy σ,encodeTy τ,i,j] := by
        rw [encodeTerm,exact_ExactTaggedNodeCodec.1,codeQ,codeU]
      rw [rawAt S K Γ σ τ i j hq hu,decodedAt S K Γ σ τ i j Q U hq hu hQ hU,← termCode,
        exact_LeastRepresentative,exact_TermCodec.2.1]
      simp only [Option.bind_eq_bind,Option.bind_some,resultPack]

#print axioms exact_CanonicalLiteralApplication
end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchCanonicalAppProof
