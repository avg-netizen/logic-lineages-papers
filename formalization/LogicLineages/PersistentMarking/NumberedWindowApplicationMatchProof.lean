import LogicLineages.PersistentMarking.NumberedWindowApplicationMatchTargets
import LogicLineages.PersistentMarking.NumberedWindowApplicationGraphChecks
import LogicLineages.PersistentMarking.NumberedWindowClassApplicationPathChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticPathClassProof
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAddressAlgorithmChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAtomCodeChecks

namespace LogicLineages.PersistentMarking.NumberedWindowApplicationMatchProof
open Spine NumberedWindowSyntax NumberedWindowExternalApplication
open NumberedWindowApplicationMatch NumberedWindowApplicationMatchTargets
open NumberedWindowAddressApplication NumberedWindowApplicationGraphChecks
open NumberedWindowAddressApplicationChecks NumberedWindowAddressApplicationTargets
open NumberedWindowArithmeticAllContextBits NumberedWindowArithmeticClassAddress
open NumberedWindowArithmeticClassAddressProof NumberedWindowArithmeticPathCheckBits
open NumberedWindowArithmeticScalarTargets NumberedWindowArithmeticTyCode
open NumberedWindowArithmeticAddressAlgorithmChecks NumberedWindowClassApplicationPathChecks
open NumberedWindowPathWitnessClassCode NumberedWindowArithmeticCodecLaws
open NumberedWindowAddressAlgorithm (addressView)
open NumberedWindowArithmeticAddressAlgorithmTargets (address)

private theorem view (a : ClassAddress) : addressView (encodeAddress a) = some (address a) := by
  rw [exact_ExactAddressView,round]
  rfl

private theorem arrow (σ τ : Ty) :
    arrowView (encodeTy (.arrow σ τ)) = some (encodeTy σ,encodeTy τ) := by
  simp [encodeTy,arrowView,← NumberedWindowActualPairAlgorithmChecks.currentDecoder,pairRound]

private theorem knownArrow {S : Signature} {K Γ : List Ty} {σ τ : Ty}
    (hk : DecisionSourceUniverse.Closed K) {i j argument value certificate : Nat}
    (positive : positiveClassPathCodeBit S K Γ (.arrow σ τ) i certificate j = true)
    (later : graph (fixed S K) (encodeAddress ⟨Γ,.arrow σ τ,j⟩) argument value = true) :
    ∃ before output,
      matchingCertificate (fixed S K) (encodeAddress ⟨Γ,.arrow σ τ,i⟩) argument certificate =
        some (before,output) ∧
      graph (fixed S K) (encodeAddress ⟨Γ,.arrow σ τ,i⟩) argument before = true ∧
      addressRSBit S K before output value = true := by
  obtain ⟨q,r,hq,hr,_⟩ :=
    (NumberedWindowArithmeticPathClassProof.path S K Γ (.arrow σ τ) i j hk).mp ⟨certificate,positive⟩
  obtain ⟨a,u,k,argumentCode,hu,valueCode,hv⟩ :=
    (exact_ClassApplicationGraph S K Γ σ τ hk r j hr argument value).mp later
  obtain ⟨x,hx⟩ := existsCode S K Γ τ hk (appClass hk q u)
  let before := encodeAddress ⟨Γ,τ,x⟩
  have graphBefore : graph (fixed S K) (encodeAddress ⟨Γ,.arrow σ τ,i⟩) argument before = true :=
    (exact_ClassApplicationGraph S K Γ σ τ hk q i hq argument before).mpr
      ⟨a,u,x,argumentCode,hu,rfl,hx⟩
  have computedApplication :
      application (fixed S K) (encodeAddress ⟨Γ,.arrow σ τ,i⟩) argument = some before :=
    beq_iff_eq.mp graphBefore
  obtain ⟨y,output,_,_,_,_,_,_,_,computedPath,validPath,hy⟩ :=
    exact_PositiveClassPathLift S K Γ σ τ hk q r u i j a x certificate hq hr hu hx positive
  have sameResult : y = k := sameCode hk hy hv
  subst y
  have argumentView : addressView argument = some (address ⟨Γ,σ,a⟩) := by
    rw [argumentCode]
    exact view _
  have beforeView : addressView before = some (address ⟨Γ,τ,x⟩) := view _
  refine ⟨before,output,?_,graphBefore,?_⟩
  · rw [matchingCertificate,view ⟨Γ,.arrow σ τ,i⟩]
    simp only [Option.bind_eq_bind,Option.bind_some,address,arrow]
    rw [argumentView]
    simp only [Option.bind_some,address,computedApplication,beforeView,computedPath,Option.pure_def]
  · rw [valueCode]
    simp only [before,addressRSBit,round,decide_true,Bool.true_and]
    exact validPath

theorem matching : ExactBackwardAddressMatching := by
  intro S K hk source target argument value certificate positive later
  cases hs : decodeAddress source with
  | none => simp [addressRSBit,hs] at positive
  | some f =>
    cases ht : decodeAddress target with
    | none => simp [addressRSBit,hs,ht] at positive
    | some g =>
      rcases f with ⟨Γ,ft,i⟩
      rcases g with ⟨Δ,gt,j⟩
      simp only [addressRSBit,hs,ht,Bool.and_eq_true,decide_eq_true_eq] at positive
      have sameContext : Γ = Δ := positive.1.1
      have sameType : ft = gt := positive.1.2
      subst Δ
      subst gt
      rw [← read ht] at later
      rw [← read hs]
      cases ft with
      | ground =>
          have applied : application (fixed S K) (encodeAddress ⟨Γ,.ground,j⟩) argument = some value :=
            beq_iff_eq.mp later
          rw [exact_DecodedApplication S K] at applied
          unfold decodedApplication at applied
          rw [round] at applied
          cases ha : decodeAddress argument <;> simp [ha] at applied
      | arrow σ τ => exact knownArrow hk positive.2 later

end LogicLineages.PersistentMarking.NumberedWindowApplicationMatchProof
