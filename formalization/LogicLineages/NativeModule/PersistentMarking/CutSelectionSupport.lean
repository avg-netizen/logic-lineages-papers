module

public import LogicLineages.NativeModule.PersistentMarking.CutSelectionTargets
public import LogicLineages.NativeModule.PersistentMarking.CutOwnerProof
public import LogicLineages.NativeModule.PersistentMarking.ApplicationCovarianceProof

@[expose] public section

namespace LogicLineages.PersistentMarking.CutSelectionSupport
open Spine

theorem tupleRelated {S : Signature} {f g : Head} {sb se tb te : Args} {ρ : Ty}
    (root : CutOwnerSyntax.Root S f sb se g tb te)
    (hp : PaperTerm S (.marked f ρ sb se) ρ) (ht : PaperTerm S (.marked g ρ tb te) ρ)
    {domains : List Ty} {args : Args} (h : PrefixTuple g tb te domains args) :
    _root_.Nonempty (ExtendedOrderedTree S (ownerCopies f sb se domains) args) := by
  induction h with
  | nil => exact ⟨.orderedNil⟩
  | cons hcopy hrest ih =>
    obtain ⟨hedge⟩ := CutOwnerProof.wholePrefix S f sb se g tb te ρ _ _ root hp ht hcopy
    obtain ⟨hrest'⟩ := ih
    exact ⟨.orderedCons hedge hrest'⟩

theorem selectedValid {S : Signature} {g : Head} {τ : Ty} {tb te : Args} {i : Nat} {q : Expr}
    (ht : PaperTerm S (.marked g τ tb te) τ) (ha : At tb i q ∨ At te i q) : Valid S q := by
  exact ha.elim (fun h => UnarySelectionProof.atValid h ht.2.2.1) (fun h => UnarySelectionProof.atValid h ht.2.2.2)
end LogicLineages.PersistentMarking.CutSelectionSupport
