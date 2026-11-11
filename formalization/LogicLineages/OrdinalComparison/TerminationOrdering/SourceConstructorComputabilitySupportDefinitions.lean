module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceRankedConstructorComputabilityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceZeroNumberedComputabilityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourcePrimitiveMultisetQuotientProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorPrimaryMeasuresProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceLambdaComputabilityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.RankedPrecedenceChainsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputability
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedLeastCodeRepresentative OrdinaryArithmeticQuotient PositiveArithmeticOperators
open PositiveArithmeticLeastSet SourceComputabilityFormula SourceZeroNumberedComputability

/-- Abbreviation only: the actual logical relation at the original calibrated tuple. -/
abbrev CodeC (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (context : Nat)
    (scalar : Positive (Fin 2)) (tau : Ty) (x : Nat) : Prop :=
  Computable n arity Gamma (fun x => x ∈ leastSet scalar context) context tau x

abbrev TermC {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} (context : Nat)
    (ctx : Context n) (scalar : Positive (Fin 2)) {tau : Ty}
    (q : AuxTerm (Fin n) arity Gamma tau) : Prop :=
  CodeC n arity Gamma context scalar tau (representativeCode ctx.1.1 ctx.1.2 ⟨tau,q⟩)

abbrev ArgumentsC {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} (context : Nat)
    (ctx : Context n) (scalar : Positive (Fin 2)) {types : List Ty}
    (args : AuxArguments (Fin n) arity Gamma types) : Prop :=
  ∀ p ∈ argumentCodes ctx.1.1 ctx.1.2 args, CodeC n arity Gamma context scalar p.1 p.2

abbrev ArgumentValues {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (ctx : Context n) {types : List Ty} (args : AuxArguments (Fin n) arity Gamma types) : List Nat :=
  (argumentCodes ctx.1.1 ctx.1.2 args).map Prod.snd

abbrev Descent {n : Nat} (arity : Fin n → Nat) (Gamma : List Ty) (ctx : Context n) :
    List Nat → List Nat → Prop :=
  DirectMultisetAccessibility.ReverseDirect
    (QuotientDominationCertificates.relation n arity ctx.1.1 ctx.1.2 Gamma ctx.2)
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputability
