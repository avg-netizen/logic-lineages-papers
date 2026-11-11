module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceZeroNumberedEdgeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceZeroNumberedAccessibilitySupportProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedLeastCodeRepresentative NumberedQuotientPaths SourceZeroNumberedComputability
open OrdinaryArithmeticQuotient PositiveArithmeticOperators SourceComputabilityArrowLeastSupportProof

theorem replacementDirect {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)} {S Gamma : List Ty}
    {above : Fin n → Fin n → Prop} {source target : List (Ty × Nat)}
    (h : OneMemberReplacement n arity symbols S above Gamma source target) :
    DirectMultisetPresentation.Direct (PositivePath (QuotientEdge n arity symbols S above Gamma))
      (source.map Prod.snd) (target.map Prod.snd) := by
  obtain ⟨kept,sigma,x,y,hs,ht,he⟩ := h
  refine ⟨kept.map Prod.snd,[x],[y],?_,?_,by simp,?_⟩
  · simpa only [List.map_append,List.map_cons,List.map_nil] using hs.map Prod.snd
  · simpa only [List.map_append,List.map_cons,List.map_nil] using ht.map Prod.snd
  · intro z hz
    have hz' : z = y := List.mem_singleton.mp hz
    subst z
    exact ⟨x,by simp,PositivePath.step he⟩

theorem replacementPreservesMembers {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)} {S Gamma : List Ty}
    {above : Fin n → Fin n → Prop} {source target : List (Ty × Nat)}
    (P : Ty → Nat → Prop)
    (hdown : ∀ sigma x y, P sigma x → QuotientEdge n arity symbols S above Gamma x y → P sigma y)
    (h : OneMemberReplacement n arity symbols S above Gamma source target)
    (hm : ∀ p ∈ source, P p.1 p.2) : ∀ p ∈ target, P p.1 p.2 := by
  obtain ⟨kept,sigma,x,y,hs,ht,he⟩ := h
  intro p hp
  rcases List.mem_append.mp (ht.mem_iff.mp hp) with hp | hp
  · exact hm p (hs.mem_iff.mpr (List.mem_append_left _ hp))
  · have hp' : p = (sigma,y) := List.mem_singleton.mp hp
    subst p
    apply hdown sigma x y _ he
    exact hm (sigma,x) (hs.mem_iff.mpr (by simp))

theorem quotientAccessible (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context : Nat) (ctx : Context n) (hc : Encodable.decode context = some ctx)
    (x : Nat) (hacc : Acc (fun successor source => encodedR n arity Gamma context source successor) x) :
    Acc (fun successor source => QuotientDominationCertificates.relation n arity ctx.1.1 ctx.1.2 Gamma ctx.2 source successor) x := by
  induction hacc with
  | intro x h ih =>
    refine Acc.intro x ?_
    intro y hy
    exact ih y ((relationCalibration n arity Gamma context ctx hc x y).mpr hy)
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceZeroNumberedAccessibilitySupportProof
