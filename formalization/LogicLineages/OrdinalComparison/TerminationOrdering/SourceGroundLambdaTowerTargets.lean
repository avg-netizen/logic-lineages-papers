module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundLambdaTowerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundLambdaTowerTargets
open Source NumberedRewriteSyntax NumberedFiniteUniverse NumberedLeastCodeRepresentative
open OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators PositiveArithmeticAccessibility PositiveArithmeticLeastSet
open SourceComputabilityFormula SourceGroundContextTower SourceGroundLambdaTower

def ActualGroundLambdaTowerSubstitution : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma Delta : List Ty)
    (context : Nat) (ctx : Context n) (k : Nat) (scalar : Nat → Positive (Fin 2)),
  Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
  (∀ j : Nat, j ≤ k → Calibrates (scalar j) context
    (encodedScalar n arity (groundContext j Delta) context) (encodedR n arity (groundContext j Delta) context)) →
  ∀ theta : NumberedRewriteSyntax.Substitution (Fin n) arity Gamma Delta,
  NumberedUniverseBindingTargets.GoodSubstitution (fun t => t ∈ ctx.1.2) (HeadInWindow arity ctx.1.1 ctx.1.2) theta →
  (∀ (j : Nat), j ≤ k → ∀ (upsilon : Ty) (v : Variable Gamma upsilon),
    Computable n arity (groundContext j Delta) (fun x => x ∈ leastSet (scalar j) context) context upsilon
      (representativeCode ctx.1.1 ctx.1.2 ⟨upsilon,rename (theta v) (groundRenaming j Delta)⟩)) →
  ∀ (tau : Ty) (q : AuxTerm (Fin n) arity Gamma tau),
  InUniverse ctx.1.1 ctx.1.2 q → GroundLambdaFragment k q →
  Computable n arity Delta (fun x => x ∈ leastSet (scalar 0) context) context tau
    (representativeCode ctx.1.1 ctx.1.2 ⟨tau,substitute q theta⟩)
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundLambdaTowerTargets
