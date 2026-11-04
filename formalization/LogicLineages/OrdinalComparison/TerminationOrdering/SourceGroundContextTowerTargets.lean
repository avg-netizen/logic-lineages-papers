module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundContextTowerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundContextTowerTargets
open Source NumberedRewriteSyntax NumberedFiniteUniverse NumberedLeastCodeRepresentative
open OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators PositiveArithmeticAccessibility PositiveArithmeticLeastSet
open SourceComputabilityFormula SourceGroundContextTower

def ActualGroundContextEquation : Prop := ∀ (k : Nat) (Gamma : List Ty),
  groundContext k Gamma = List.replicate k Ty.ground ++ Gamma

def ActualGroundRenamingEquations : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty)
    (tau : Ty) (q : AuxTerm Symbol arity Gamma tau),
  rename q (groundRenaming 0 Gamma) = q ∧
  ∀ k : Nat, rename q (groundRenaming (k + 1) Gamma) =
    rename (rename q (groundRenaming k Gamma)) (Renaming.weaken (groundContext k Gamma) .ground)

def ActualGroundTowerComputability : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context : Nat) (ctx : Context n) (k : Nat) (scalar : Nat → Positive (Fin 2)),
  Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
  (∀ j : Nat, j ≤ k → Calibrates (scalar j) context
    (encodedScalar n arity (groundContext j Gamma) context) (encodedR n arity (groundContext j Gamma) context)) →
  ∀ q : AuxTerm (Fin n) arity Gamma .ground, InUniverse ctx.1.1 ctx.1.2 q →
  (Computable n arity Gamma (fun x => x ∈ leastSet (scalar 0) context) context .ground
      (representativeCode ctx.1.1 ctx.1.2 ⟨.ground,q⟩) ↔
    Computable n arity (groundContext k Gamma) (fun x => x ∈ leastSet (scalar k) context) context .ground
      (representativeCode ctx.1.1 ctx.1.2 ⟨.ground,rename q (groundRenaming k Gamma)⟩))
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundContextTowerTargets
