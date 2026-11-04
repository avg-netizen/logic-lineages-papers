module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceArithmeticAccessibilityTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceArithmeticAccessibilityProof
open PositiveArithmeticOperators PositiveArithmeticLeastSet PositiveArithmeticAccessibility
open OrdinaryArithmeticCarrier OrdinaryArithmeticDirect SourceArithmeticAccessibility

theorem encodedScalarPreservation : SourceArithmeticAccessibilityTargets.ActualEncodedScalarPreservation := by
  intro n arity Gamma context hclosed x y _ hR
  rcases hclosed with ⟨ctx,hctx,hc⟩
  rcases hR with ⟨ctx',hctx',hr⟩
  have he : ctx=ctx' := Option.some.inj (hctx.symm.trans hctx')
  subst ctx'
  have ht := (QuotientDirectCarrierProof.positivePathCarrier n arity ctx.1.1 ctx.1.2 hc Gamma ctx.2 x y hr).2
  exact ⟨ctx,hctx,ht⟩

theorem encodedListPreservation : SourceArithmeticAccessibilityTargets.ActualEncodedListPreservation := by
  intro n arity Gamma context hclosed x y hx hD
  rcases hclosed with ⟨ctx,hctx,hc⟩
  rcases hD with ⟨ctx',ss,ts,hctx',hss,hts,hd⟩
  have he : ctx=ctx' := Option.some.inj (hctx.symm.trans hctx')
  subst ctx'
  rcases hx with ⟨ctx'',values,hctx'',hvalues,hgood⟩
  have he : ctx=ctx'' := Option.some.inj (hctx.symm.trans hctx'')
  subst ctx''
  have hv : ss=values := Option.some.inj (hss.symm.trans hvalues)
  subst values
  have ht := QuotientDirectCarrierProof.directCarrierPreservation n arity ctx.1.1 ctx.1.2 hc Gamma ctx.2 ss ts hd hgood
  exact ⟨ctx,ts,hctx,hts,ht⟩

theorem sourceLeastAccessibility : SourceArithmeticAccessibilityTargets.ActualSourceLeastAccessibility := by
  intro n arity Gamma
  obtain ⟨scalar,multiset,h⟩ := PositiveArithmeticOperatorsProof.sourcePositiveOperators n arity Gamma
  have hs (context : Nat) : Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) :=
    fun P x => (h P context x).1
  have hm (context : Nat) : Calibrates multiset context (encodedList n arity Gamma context) (encodedDirect n arity Gamma context) :=
    fun P x => (h P context x).2
  refine ⟨scalar,multiset,(fun context => ⟨hs context,hm context⟩),?_⟩
  intro context hc x
  exact ⟨PositiveArithmeticAccessibilityProof.preservedCarrierAccessibility scalar context
      (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) (hs context)
      (encodedScalarPreservation n arity Gamma context hc) x,
    PositiveArithmeticAccessibilityProof.preservedCarrierAccessibility multiset context
      (encodedList n arity Gamma context) (encodedDirect n arity Gamma context) (hm context)
      (encodedListPreservation n arity Gamma context hc) x⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceArithmeticAccessibilityProof
