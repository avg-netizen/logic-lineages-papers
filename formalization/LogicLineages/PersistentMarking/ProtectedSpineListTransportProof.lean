import LogicLineages.PersistentMarking.ProtectedSpineCompletenessTargets

namespace LogicLineages.PersistentMarking.ProtectedSpineListTransportProof
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode
open PortNormalization ProtectedSpineAdequacyTargets ProtectedSpineCompletenessTargets ProtectedSpineLaws
open ProtectedSpineInterpreter ProtectedSpineFixedApplicationTargets
open MarkedConstructorTargets (Delete SplitList)

theorem removeTerms {qs rest : Args} {q : Expr} (h : Remove qs q rest) :
    Delete q (MarkedConstructorTests.terms qs) (MarkedConstructorTests.terms rest) := by
  induction h with
  | here => exact .here
  | there h ih => exact .there ih

theorem splitTerms {qs left right : Args} (h : Split qs left right) :
    SplitList (MarkedConstructorTests.terms qs) (MarkedConstructorTests.terms left) (MarkedConstructorTests.terms right) := by
  induction h with
  | nil => exact .nil
  | left h ih => exact .left ih
  | right h ih => exact .right ih

theorem splitTags (S : Signature) (F : Inputs S) (M : Code) (Γ : Context) {qs left right : Args}
    (h : Split qs left right) :
    SplitList (concreteTags S F M Γ qs) (concreteTags S F M Γ left) (concreteTags S F M Γ right) := by
  induction h with
  | nil => exact .nil
  | left h ih => exact .left ih
  | right h ih => exact .right ih

theorem atGet {qs : Args} {i : Nat} {q : Expr} (h : At qs i q) : qs.get i = some q := by
  induction h with
  | here => rfl
  | there h ih => exact ih

theorem atTag (S : Signature) (F : Inputs S) (M : Code) (Γ : Context) {qs : Args} {i : Nat} {q : Expr}
    (h : At qs i q) :
    (q.type,codeAt (domain F) q.type (evaluate S (domain F) F.data.sourceHeads M q) Γ ⟨[],[]⟩) ∈
      concreteTags S F M Γ qs :=
  List.mem_of_getElem? (ProtectedSpineConcreteInputProof.entry S (domain F) F.data.sourceHeads M Γ qs i q (atGet h))

theorem nonemptyTags (S : Signature) (F : Inputs S) (M : Code) (Γ : Context)
    (qs : Args) (h : Spine.Nonempty qs) : concreteTags S F M Γ qs ≠ [] := by
  cases qs with
  | nil => cases h
  | cons q qs => intro he; cases he

end LogicLineages.PersistentMarking.ProtectedSpineListTransportProof
