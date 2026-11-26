import LogicLineages.PersistentMarking.BoundBlockProof
import LogicLineages.PersistentMarking.ClosedSyntaxProof
import LogicLineages.PersistentMarking.PrefixResultProof
namespace LogicLineages.PersistentMarking.PrefixSplicingSupport
open Spine AuxiliaryReflexivityProof

theorem lookupCopy {f : Head} {base extras xs : Args} (h : PrefixCopies f base extras xs)
    (i : Nat) (v : Expr) (hv : xs.get i = some v) : ∃ σ, PrefixCopy f base extras σ v := by
  cases h with
  | nil => simp [Args.get] at hv
  | @cons q qs hc hs =>
    cases i with
    | zero =>
      simp only [Args.get,Option.some.injEq] at hv
      subst v
      exact ⟨q.type,hc⟩
    | succ i => exact lookupCopy hs i v hv
termination_by sizeOf xs

theorem insertedCall (S : Signature) (f : Head) (ρ τ σ : Ty) (base extras : Args) (v : Expr)
    (hp : PaperTerm S (.marked f ρ base extras) ρ) (hcopy : PrefixCopy f base extras σ v)
    (newer : Args) (a : Expr) (rest : Args) (hargs : PrefixCopies f base extras (.cons a rest))
    (w : Expr) (hw : w.type = τ)
    (hcall : applyAux (shift newer.length 0 v) (.cons a rest) newer = some w) :
    Refines S (.marked f τ base extras) w := by
  have href := OwnerRefinementProof.copyRefines S f ρ σ base extras v hp hcopy
  obtain ⟨href⟩ := href
  have htyped := (RefinementSubstitutionSupport.endpoints href).2.1
  have hshift := ClosedSyntaxProof.closedShift v v.type htyped newer.length
  rw [hshift] at hcall
  cases hcopy with
  | @intro pref σ hprefix =>
    cases htyped with
    | marked hb he =>
      have hbase := (ClosedSyntaxProof.bases EmptyContext 0 ClosedSyntaxProof.emptyBound base _ hb 0 newer).2
      have hextras := (ClosedSyntaxProof.extras EmptyContext 0 ClosedSyntaxProof.emptyBound pref he 0 newer).2
      cases hc : consumeTypes σ (.cons a rest) with
      | none => simp [applyAux,hc] at hcall
      | some υ =>
        simp only [applyAux,hc,Option.map_some,hbase,hextras,Option.some.injEq] at hcall
        subst w
        change υ = τ at hw
        subst τ
        exact PrefixResultProof.prefixResult S f ρ υ base extras pref (.cons a rest) hp hprefix hargs
end LogicLineages.PersistentMarking.PrefixSplicingSupport
