module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitSubstitutionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.InterpretedArgumentAppend
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment CoherentConstructorLattice FunctionalSpineActions ConfinedStructuralInterpretation TypedExtraDownsets

def packedValues {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {Γ types : List Ty} (args : Arguments Symbol arity Γ types) (ha : ArgumentsConfined I args)
    (M : Constructors I) (P : World I) (ρ : Environment I Γ P) : List (Packed I P) :=
  packArguments types (argumentTypeList args ha) (evaluateArguments (buildArguments I args ha) M P ρ)

end LogicLineages.OrdinalComparison.TerminationOrdering.InterpretedArgumentAppend
