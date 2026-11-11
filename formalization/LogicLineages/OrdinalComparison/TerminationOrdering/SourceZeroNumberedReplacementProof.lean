module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceZeroNumberedShapeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceZeroNumberedReplacementProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedWindowReduction NumberedWindowEquivalence NumberedLeastCodeRepresentative NumberedQuotientPaths
open SourceZeroNumberedComputability

theorem replacementPerm {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)} {S Gamma : List Ty}
    {above : Fin n → Fin n → Prop} {a b c d : List (Ty × Nat)}
    (ha : a.Perm b) (hb : c.Perm d) (h : OneMemberReplacement n arity symbols S above Gamma b d) :
    OneMemberReplacement n arity symbols S above Gamma a c := by
  obtain ⟨kept,sigma,x,y,hs,ht,he⟩ := h
  exact ⟨kept,sigma,x,y,ha.trans hs,hb.trans ht,he⟩

theorem replacementAppendLeft {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)} {S Gamma : List Ty}
    {above : Fin n → Fin n → Prop} {a b : List (Ty × Nat)}
    (h : OneMemberReplacement n arity symbols S above Gamma a b) (c : List (Ty × Nat)) :
    OneMemberReplacement n arity symbols S above Gamma (c ++ a) (c ++ b) := by
  obtain ⟨kept,sigma,x,y,hs,ht,he⟩ := h
  refine ⟨c ++ kept,sigma,x,y,?_,?_,he⟩
  · simpa only [List.append_assoc] using hs.append_left c
  · simpa only [List.append_assoc] using ht.append_left c

theorem replacementAppendRight {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)} {S Gamma : List Ty}
    {above : Fin n → Fin n → Prop} {a b : List (Ty × Nat)}
    (h : OneMemberReplacement n arity symbols S above Gamma a b) (c : List (Ty × Nat)) :
    OneMemberReplacement n arity symbols S above Gamma (a ++ c) (b ++ c) := by
  exact replacementPerm List.perm_append_comm List.perm_append_comm (replacementAppendLeft h c)

theorem argumentStepReplacement {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)} {S : List Ty}
    {above : Fin n → Fin n → Prop} {Gamma types : List Ty}
    {a b : AuxArguments (Fin n) arity Gamma types}
    (h : WindowArgumentStep (Fin n) arity symbols S above Gamma types a b) :
    NumberedUniverseBindingTargets.GoodArguments (fun t => t ∈ S) (HeadInWindow arity symbols S) a →
    OneMemberReplacement n arity symbols S above Gamma (argumentCodes symbols S a) (argumentCodes symbols S b) := by
  induction types with
  | nil => cases h
  | cons sigma types ih => cases h with
    | head q r rest hs =>
      intro ha
      refine ⟨argumentCodes symbols S rest,sigma,
        representativeCode symbols S ⟨sigma,q⟩,representativeCode symbols S ⟨sigma,r⟩,?_,?_,?_⟩
      · simpa only [argumentCodes,argumentList,List.map_cons,List.singleton_append] using
          (List.perm_append_comm :
            ([(sigma,representativeCode symbols S ⟨sigma,q⟩)] ++ argumentCodes symbols S rest).Perm
            (argumentCodes symbols S rest ++ [(sigma,representativeCode symbols S ⟨sigma,q⟩)]))
      · simpa only [argumentCodes,argumentList,List.map_cons,List.singleton_append] using
          (List.perm_append_comm :
            ([(sigma,representativeCode symbols S ⟨sigma,r⟩)] ++ argumentCodes symbols S rest).Perm
            (argumentCodes symbols S rest ++ [(sigma,representativeCode symbols S ⟨sigma,r⟩)]))
      · exact ⟨sigma,q,r,⟨ha.1.1,ha.2.1⟩,hs,rfl,rfl⟩
    | tail q rest target hs =>
      intro ha
      simpa only [argumentCodes,argumentList,List.map_cons,List.singleton_append] using
        replacementAppendLeft (ih hs ⟨ha.1.2,ha.2.2⟩)
          [(sigma,representativeCode symbols S ⟨sigma,q⟩)]
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceZeroNumberedReplacementProof
