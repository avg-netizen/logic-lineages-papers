import LogicLineages.PersistentMarking.NumberedWindowNeutralApplicationAddressTargets
import LogicLineages.PersistentMarking.NumberedWindowExternalNeutralTargets
import LogicLineages.PersistentMarking.NumberedWindowRawWitnessLaws
import LogicLineages.PersistentMarking.NumberedWindowArithmeticScalarChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAddressAlgorithmChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticClassAddressProof
import LogicLineages.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticNodeProof

namespace LogicLineages.PersistentMarking.NumberedWindowNeutralApplicationCertificateProof
open Spine NumberedWindowSyntax NumberedWindowExternalNeutralTargets
open NumberedWindowNeutralApplicationAddress NumberedWindowRawWitnessBits NumberedWindowRawWitnessRootBits
open NumberedWindowArithmeticClassAddress NumberedWindowArithmeticClassAddressProof
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticTermCodeChecks
open NumberedWindowArithmeticRawWitnessCode NumberedWindowArithmeticPathCode
open NumberedWindowClassPathWitnessBits NumberedWindowArithmeticTyCode NumberedWindowArithmeticBinderCode
open NumberedWindowArithmeticLeastClass NumberedWindowArithmeticScalarTargets
open NumberedWindowArithmeticScalarChecks NumberedWindowArithmeticAddressAlgorithmChecks
open NumberedWindowArithmeticFieldAlgorithmChecks NumberedWindowArithmeticNodeProof
open NumberedWindowRawWitnessLaws (termEqTrue)
open NumberedWindowArithmeticAddressAlgorithmTargets (address)
open NumberedWindowPositivePathAlgorithm (edgeView)
open NumberedWindowFieldAlgorithm (pack unpackNode)

theorem suppliedCases {S : Signature} {K : List Ty} {σ τ : Ty} {Q A R : NTerm}
    {w : RawWitness} (hn : NonLambda Q)
    (h : rawBit S K w (.auxApp σ τ Q A) R = true) :
    R = .bottom τ ∨
      ∃ (next : NTerm) (child : RawWitness),
        w = .auxFunction child ∧ R = .auxApp σ τ next A ∧ rawBit S K child Q next = true := by
  cases w with
  | root root =>
    cases root with
    | beta =>
      cases Q <;> try (simp only [rawBit,rootBit,Bool.false_eq_true] at h)
      case lam ρ body => exact (hn ρ body rfl).elim
    | bottom =>
      simp only [rawBit,rootBit,Bool.and_eq_true,termEqTrue] at h
      exact Or.inl h.2
    | _ => simp [rawBit,rootBit] at h
  | auxFunction child =>
    cases R <;> try (simp only [rawBit,Bool.false_eq_true] at h)
    case auxApp ρ υ next B =>
      simp only [rawBit,Bool.and_eq_true,decide_eq_true_eq,termEqTrue] at h
      obtain ⟨⟨⟨hd,hc⟩,ha⟩,inner⟩ := h
      subst ρ
      subst υ
      subst B
      exact Or.inr ⟨next,child,rfl,rfl,inner⟩
  | _ => simp [rawBit] at h

private theorem appField (σ τ : Ty) (Q A : NTerm) :
    functionField (encodeTerm (.auxApp σ τ Q A)) = some (encodeTerm Q) := by
  simp [functionField,encodeTerm,← exact_ExactTaggedNodeCodec.2,nodeRound]

private theorem witnessChild (w : RawWitness) :
    functionChild (encodeWitness (.auxFunction w)) = some (encodeWitness w) := by
  simp [functionChild,encodeWitness,← exact_ExactTaggedNodeCodec.2,nodeRound]

private theorem edgeFields (e : ClassEdgeWitness) :
    edgeView (encodeClassEdge e) = some (encodeTerm e.source,encodeWitness e.witness,encodeTerm e.target) := by
  simp [edgeView,encodeClassEdge,← exact_ExactTaggedNodeCodec.2,nodeRound]

private theorem binders (Γ : List Ty) : pack (Γ.map encodeTy) = encodeBinders Γ := by
  induction Γ with
  | nil => rfl
  | cons t Γ ih =>
      simp [pack,encodeBinders,ih,NumberedWindowActualPairAlgorithmChecks.currentPair]

theorem literal (S : Signature) (K Γ : List Ty) (σ τ : Ty) (i nextCode : Nat)
    (Q R A : NTerm) (child : RawWitness)
    (h : leastCode S K Γ (.arrow σ τ) R = some nextCode) :
    functionWitness (fixed S K) (encodeAddress ⟨Γ,.arrow σ τ,i⟩)
      (encodeClassEdge ⟨.auxApp σ τ Q A,.auxApp σ τ R A,.auxFunction child⟩) =
        some (encodeAddress ⟨Γ,.arrow σ τ,nextCode⟩,encodeClassEdge ⟨Q,R,child⟩) := by
  simp only [functionWitness,exact_ExactAddressView,round,Option.map_some,
    Option.bind_eq_bind,Option.bind_some,address,edgeFields,appField,witnessChild]
  rw [exact_LeastRepresentative S K Γ (.arrow σ τ) (encodeTerm R)]
  simp only [exact_TermCodec.2.1,Option.bind_some,h,Option.pure_def,encodeAddress,encodeClassEdge,
    exact_ExactTaggedNodeCodec.1,binders]

end LogicLineages.PersistentMarking.NumberedWindowNeutralApplicationCertificateProof
