module
public import LogicLineages.OrdinalComparison.TerminationOrdering.InterpretedArgumentAppendDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.InterpretedArgumentAppendTargets
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment CoherentConstructorLattice FunctionalSpineActions ConfinedStructuralInterpretation TypedExtraDownsets InterpretedArgumentAppend

def AppendConfinement : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ xs ys : List Ty)
    (a : Arguments Symbol arity Γ xs) (b : Arguments Symbol arity Γ ys),
    ArgumentsConfined I a → ArgumentsConfined I b → ArgumentsConfined I (appendArguments a b)

def OrderedPackedAppend : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ xs ys : List Ty)
    (a : Arguments Symbol arity Γ xs) (b : Arguments Symbol arity Γ ys)
    (ha : ArgumentsConfined I a) (hb : ArgumentsConfined I b) (hab : ArgumentsConfined I (appendArguments a b))
    (M : Constructors I) (P : World I) (ρ : Environment I Γ P),
    packedValues (appendArguments a b) hab M P ρ=packedValues a ha M P ρ ++ packedValues b hb M P ρ

def DownclosureAppend : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (P : World I) (E : Extras I P) (xs ys : List (Packed I P)),
    TypedExtraAppendProof.appendExtras (TypedExtraAppendProof.appendExtras E xs) ys=
      TypedExtraAppendProof.appendExtras E (xs++ys)

end LogicLineages.OrdinalComparison.TerminationOrdering.InterpretedArgumentAppendTargets
