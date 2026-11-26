module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableTargets
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction
open NumberedUniverseBindingTargets NumberedPrimarySubstitution NumberedBottomVariable

def ActualLiftBottomOrVariable : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta : List Ty) (sigma : Ty)
    (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta),
    BottomOrVariable theta → BottomOrVariable (liftSubstitution (sigma := sigma) theta)

def ActualBottomOrVariableGood : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (K : Ty → Prop) (H : Head Symbol → Prop) (Gamma Delta : List Ty)
    (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta),
    BottomOrVariable theta → GoodSubstitution K H theta

/-- The erased binder's type is arbitrary, not required to belong to S. -/
def ActualSingleBottomOrVariable : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma : List Ty) (sigma : Ty),
    BottomOrVariable (singleSubstitution (AuxTerm.bottom sigma : AuxTerm Symbol arity Gamma sigma))

/-- Inverse lifting is existential at the original endpoint. It does not
reflect relations between two previously fixed erasure preimages. -/
def ActualFiniteMarkInverse : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta : List Ty) (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta),
    BottomOrVariable theta → ∀ (label : Nat) (tau : Ty)
      (q : AuxTerm Symbol arity Gamma tau) (r : AuxTerm Symbol arity Delta tau),
    finiteMark label (substitute q theta) = some r →
    ∃ q' : AuxTerm Symbol arity Gamma tau,
      finiteMark label q = some q' ∧ substitute q' theta = r

def ActualPrimitiveMarkInverse : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta : List Ty) (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta),
    BottomOrVariable theta → ∀ (q : Packed Symbol arity Gamma) (r : Packed Symbol arity Delta),
    PrimitiveMark Symbol arity Delta (substitutePacked theta q) r →
    ∃ q' : Packed Symbol arity Gamma,
      PrimitiveMark Symbol arity Gamma q q' ∧ substitutePacked theta q' = r

/-- The removed multiset remains nonempty. Occurrences and multiplicities are
lifted through map-permutation, without an injectivity hypothesis. -/
def ActualPrimitiveMultisetInverse : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta : List Ty) (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta),
    BottomOrVariable theta → ∀ (source : List (Packed Symbol arity Gamma))
      (target : List (Packed Symbol arity Delta)),
    PrimitiveMultiset (source.map (substitutePacked theta)) target →
    ∃ target' : List (Packed Symbol arity Gamma),
      PrimitiveMultiset source target' ∧ target'.map (substitutePacked theta) = target

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableTargets
