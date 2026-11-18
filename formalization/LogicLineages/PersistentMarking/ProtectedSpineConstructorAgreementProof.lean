import LogicLineages.PersistentMarking.ProtectedSpineAgreementTargets
import LogicLineages.PersistentMarking.ProtectedSpineHeadProof
import LogicLineages.PersistentMarking.ProtectedSpineVariableProof

namespace LogicLineages.PersistentMarking.ProtectedSpineConstructorAgreementProof
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode
open ProtectedSpineEnvironment ProtectedSpineLaws ProtectedSpineAgreementTargets ProtectedSpineInterpreterCore
open ProtectedSpineHeadProof (headEvaluation)
open ProtectedSpineVariableProof (lookupEvaluation)

def ArgumentsAgree (E : Environment) (R : FrameRelation) (as bs : Arguments) : Prop :=
  ∀ Γ a b, InputValid E Γ a → InputValid E Γ b → R Γ a b →
    argumentValues as Γ a = argumentValues bs Γ b

theorem cons (E : Environment) (σ : Ty) (ev ev' : Evaluation) (as bs : Arguments)
    (R : FrameRelation) (P : Nat → Nat → Prop) (hv : Agreement E σ ev ev' R P)
    (ht : ArgumentsAgree E R as bs) :
    ArgumentsAgree E R (ProtectedSpineArgumentProof.consArguments E σ ev as)
      (ProtectedSpineArgumentProof.consArguments E σ ev' bs) := by
  intro Γ a b ha hb hr
  change (σ,codeAt E σ ev Γ a) :: argumentValues as Γ a =
    (σ,codeAt E σ ev' Γ b) :: argumentValues bs Γ b
  have hc : codeAt E σ ev Γ a = codeAt E σ ev' Γ b :=
    HereditaryEncodingCongruenceProof.congruence E σ Γ _ _ (hv.value Γ a b ha hb hr)
  rw [hc,ht Γ a b ha hb hr]

theorem head (marked : Bool) (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (f : Head) (σ : Ty) (as bs es fs : Arguments) (R : FrameRelation) (P : Nat → Nat → Prop)
    (hb : ArgumentsAgree E R as bs) (he : ArgumentsAgree E R es fs) :
    Agreement E σ (headEvaluation marked S E H M f σ as es)
      (headEvaluation marked S E H M f σ bs fs) R P := by
  have hp : ∀ Γ a b, InputValid E Γ a → InputValid E Γ b → R Γ a b →
      ProtectedSpineHeadParameterProof.parameterAt E f σ as es Γ a =
        ProtectedSpineHeadParameterProof.parameterAt E f σ bs fs Γ b := by
    intro Γ a b ha hb' hr
    unfold ProtectedSpineHeadParameterProof.parameterAt
    rw [hb Γ a b ha hb' hr,he Γ a b ha hb' hr]
  constructor
  · intro Γ a b ha hb' hr
    rw [ProtectedSpineHeadProof.valueEq,ProtectedSpineHeadProof.valueEq,hp Γ a b ha hb' hr]
    exact HereditaryValueEqualityProof.refl E σ Γ _
  · intro Γ a b k l ds τ xs ha hb' hr _ _ _
    cases ds with
    | nil => rfl
    | cons d ds =>
      cases xs with
      | nil => rfl
      | cons x xs =>
        let pa := ProtectedSpineHeadParameterProof.parameterAt E f σ as es Γ a
        let pb := ProtectedSpineHeadParameterProof.parameterAt E f σ bs fs Γ b
        change originalHeadCall E H M Γ f σ pa.2.2.2.1 pa.2.2.2.2 (d::ds) (x::xs) τ =
          originalHeadCall E H M Γ f σ pb.2.2.2.1 pb.2.2.2.2 (d::ds) (x::xs) τ
        rw [show pa = pb from hp Γ a b ha hb' hr]

theorem lookup (E : Environment) (σ : Ty) (get : Context → Assignments → Code)
    (blocked : Nat → Bool) (R : FrameRelation) (P : Nat → Nat → Prop)
    (hget : ∀ Γ a b, R Γ a b → get Γ a = get Γ b)
    (hblock : ∀ k l, P k l → blocked k = blocked l) :
    Agreement E σ (lookupEvaluation E σ get blocked) (lookupEvaluation E σ get blocked) R P := by
  constructor
  · intro Γ a b _ _ h
    change HereditaryDomainSemantics.ValueEq E σ Γ
      (HereditaryDomainSemantics.decode E σ Γ (get Γ a))
      (HereditaryDomainSemantics.decode E σ Γ (get Γ b))
    rw [hget Γ a b h]
    exact HereditaryValueEqualityProof.refl E σ Γ _
  · intro Γ a b k l ds τ xs _ _ hr hp hpre hx
    rw [ProtectedSpineVariableProof.callEq E σ get blocked Γ a k ds τ xs hpre hx,
      ProtectedSpineVariableProof.callEq E σ get blocked Γ b l ds τ xs hpre hx,
      hget Γ a b hr,hblock k l hp]

end LogicLineages.PersistentMarking.ProtectedSpineConstructorAgreementProof
