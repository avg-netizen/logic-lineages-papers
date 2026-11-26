import LogicLineages.PersistentMarking.ProtectedSpineAdequacyBase

namespace LogicLineages.PersistentMarking.ProtectedSpineAdequacyTypingProof
open Spine NameBridge DecisionPorts FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open ProtectedSpineAdequacyTargets ProtectedSpineAdequacyBase
open ProtectedSpineLaws ProtectedSpineInterpreter
open PortNormalization

def Ends (S : Signature) (q t : Expr) : Prop :=
  PaperTerm S q q.type ∧ PaperTerm S t q.type ∧ q.type = t.type

theorem ends (S : Signature) (q t : Expr) (σ : Ty) (hq : PaperTerm S q σ) (ht : PaperTerm S t σ) :
    Ends S q t := by
  have he := SpineShiftProof.annotationExact EmptyContext q σ hq.1
  exact ⟨he.symm ▸ hq,he.symm ▸ ht,he.trans (SpineShiftProof.annotationExact EmptyContext t σ ht.1).symm⟩

theorem weak (S : Signature) (K : List Ty) (V : List Name) (Γ : Context) (q t : Expr)
    (h : PortComparison.Weak S K V Γ q t) : Ends S q t := by
  cases h with
  | var => exact ends S _ _ _ ⟨.free,trivial⟩ ⟨.free,trivial⟩
  | abs hq ht => exact ends S _ _ _ hq ht
  | funHead hq ht _ he => exact ends S _ _ _ hq (he.symm ▸ ht)
  | put hq ht => exact ends S _ _ _ hq ht
  | select hq ht => exact ends S _ _ _ hq ht
  | fabs hq ht => exact ends S _ _ _ hq ht
  | copy hq ht => exact ends S _ _ _ hq ht
  | stat hq ht => exact ends S _ _ _ hq ht

theorem strict (S : Signature) (K : List Ty) (V : List Name) (Γ : Context) (q t : Expr)
    (h : PortComparison.Strict S K V Γ q t) : Ends S q t := by
  cases h with
  | intro hq ht => exact ends S _ _ _ hq ht

theorem taggedBit (S : Signature) (F : Inputs S) (M : Code) (Γ : Context) (q t : Expr)
    (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads)
    (hw : WellFormed F.data.types F.data.ports Γ)
    (hq : Source F Γ q) (ht : Observed F Γ t) (hty : Ends S q t) (strict : Bool)
    (hb : (if strict then (unfoldedValue S F M Γ q).strict Γ t
          else (unfoldedValue S F M Γ q).weak Γ t) = true) :
    MarkedConstructorTests.bit strict (domain F) Γ
      (q.type,codeAt (domain F) q.type (evaluate S (domain F) F.data.sourceHeads M q) Γ ⟨[],[]⟩) t = true := by
  have hbits := rootBits S F M Γ q t hm hw hq hty.1.1 ht hty.2.2
  unfold MarkedConstructorTests.bit
  refine Bool.and_eq_true_iff.mpr ⟨decide_eq_true_eq.mpr hty.2.2,?_⟩
  cases strict
  · exact hbits.1.trans hb
  · exact hbits.2.trans hb

end LogicLineages.PersistentMarking.ProtectedSpineAdequacyTypingProof
