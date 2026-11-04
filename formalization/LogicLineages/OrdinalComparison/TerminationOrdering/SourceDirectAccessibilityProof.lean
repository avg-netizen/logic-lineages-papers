module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceDirectAccessibilityTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceDirectAccessibilityProof
open OrdinaryArithmeticQuotient OrdinaryArithmeticDirect DirectMultisetAccessibility
open DirectMultisetAccessibleSubtype

theorem actualListAccessibility : SourceDirectAccessibilityTargets.ActualListAccessibility := by
  intro n arity Gamma ctx values hm
  exact DirectMultisetAccessibilityTransferProof.memberAccessibilityTransfer Nat
    (QuotientDominationCertificates.relation n arity ctx.1.1 ctx.1.2 Gamma ctx.2) values hm

theorem decodedAcc (n : Nat) (arity : Fin n → Nat) (Gamma : List Source.Ty)
    (context : Nat) (ctx : Context n) (hc : Encodable.decode context = some ctx)
    (values : List Nat)
    (hacc : Acc (ReverseDirect
      (QuotientDominationCertificates.relation n arity ctx.1.1 ctx.1.2 Gamma ctx.2)) values) :
    ∀ code : Nat, Encodable.decode code = some values →
      Acc (fun successor source => encodedDirect n arity Gamma context source successor) code := by
  induction hacc with
  | intro values h ih =>
    intro code hd
    refine Acc.intro _ ?_
    intro target hedge
    obtain ⟨ctx', ss, ts, hc', hs, ht, hrel⟩ := hedge
    have hectx : ctx = ctx' := Option.some.inj (hc.symm.trans hc')
    subst ctx'
    have hevalues : values = ss := Option.some.inj (hd.symm.trans hs)
    subst ss
    exact ih ts hrel target ht

theorem actualDecodedAccessibility : SourceDirectAccessibilityTargets.ActualDecodedAccessibility := by
  intro n arity Gamma context code ctx values hc hd hm
  exact decodedAcc n arity Gamma context ctx hc values
    (actualListAccessibility n arity Gamma ctx values hm) code hd

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceDirectAccessibilityProof
