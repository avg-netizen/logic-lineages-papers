module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityArrowLeastTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityArrowLeastSupportProof
open Source OrdinaryArithmeticQuotient OrdinaryArithmeticApplication PositiveArithmeticOperators
open NumberedLeastCodeRepresentative

theorem relationCalibration (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context : Nat) (ctx : Context n) (hc : Encodable.decode context = some ctx) (x y : Nat) :
    encodedR n arity Gamma context x y ↔
      QuotientDominationCertificates.relation n arity ctx.1.1 ctx.1.2 Gamma ctx.2 x y := by
  constructor
  · rintro ⟨ctx', hc', hr⟩
    have he : ctx = ctx' := Option.some.inj (hc.symm.trans hc')
    subst ctx'
    exact hr
  · intro hr
    exact ⟨ctx, hc, hr⟩

theorem applicationCalibration (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context : Nat) (ctx : Context n) (hc : Encodable.decode context = some ctx)
    (sigma tau : Ty) (x y : Nat) :
    decodedApplication n arity Gamma context (typeNumber sigma) (typeNumber tau) x y =
      NumberedNumericApplication.canonicalApplication n arity ctx.1.1 ctx.1.2 Gamma sigma tau x y := by
  have hs := NumberedNumericDecodingProof.typeNumericRoundTrip sigma
  have ht := NumberedNumericDecodingProof.typeNumericRoundTrip tau
  simp only [decodedApplication, hc, hs, ht]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityArrowLeastSupportProof
