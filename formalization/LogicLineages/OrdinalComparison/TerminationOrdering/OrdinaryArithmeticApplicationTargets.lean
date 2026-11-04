module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticApplicationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticApplicationTargets
open Source OrdinaryArithmeticApplication

def ActualApplicationValuePrimitive : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
  Primrec (applicationValue n arity Gamma)

def ActualPartialApplicationFormula : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
  ∃ phi : OrdinaryArithmetic.Formula (Fin 6),
    (∀ context domain codomain x y z : Nat,
      phi.Realize ![context,domain,codomain,x,y,z] ↔ decodedApplication n arity Gamma context domain codomain x y = some z) ∧
    (∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool) (sigma tau : Ty) (x y z : Nat),
      phi.Realize ![OrdinaryArithmeticQuotient.contextCode symbols S table,
        NumberedLeastCodeRepresentative.typeNumber sigma,NumberedLeastCodeRepresentative.typeNumber tau,x,y,z] ↔
      NumberedNumericApplication.canonicalApplication n arity symbols S Gamma sigma tau x y = some z)

def ActualApplicationFormulaCalibration : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
  ∃ phi : OrdinaryArithmetic.Formula (Fin 6),
    (∀ context domain codomain x y z : Nat,
      phi.Realize ![context,domain,codomain,x,y,z] ↔ decodedApplication n arity Gamma context domain codomain x y = some z) ∧
    (∀ (symbols : List (Fin n)) (S : List Ty), SubtypeClosed (fun t => t ∈ S) →
      ∀ (table : Fin n → Fin n → Bool) (sigma tau : Ty)
        (f : NumberedRewriteSyntax.AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
        (a : NumberedRewriteSyntax.AuxTerm (Fin n) arity Gamma sigma),
        NumberedFiniteUniverse.InUniverse symbols S f → NumberedFiniteUniverse.InUniverse symbols S a →
        ∀ z : Nat, phi.Realize ![OrdinaryArithmeticQuotient.contextCode symbols S table,
          NumberedLeastCodeRepresentative.typeNumber sigma,NumberedLeastCodeRepresentative.typeNumber tau,
          NumberedLeastCodeRepresentative.representativeCode symbols S ⟨.arrow sigma tau,f⟩,
          NumberedLeastCodeRepresentative.representativeCode symbols S ⟨sigma,a⟩,z] ↔
        NumberedLeastCodeRepresentative.representativeCode symbols S (NumberedQuotientApplication.applicationPacked f a) = z)

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticApplicationTargets
