module
public import LogicLineages.OrdinalComparison.TerminationOrdering.InterpretedArgumentAppendProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualOriginalApplication
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice FunctionalSpineActions ConfinedStructuralInterpretation ConfinedSubstitution SubstitutionEnvironmentSupport SourceConstructorIteration

def argumentValues {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {Γ types : List Ty} (args : Arguments Symbol arity Γ types) (ha : ArgumentsConfined I args)
    (M : Constructors I) (P : World I) (ρ : Environment I Γ P) : Values I types P :=
  evaluateArguments (buildArguments I args ha) M P ρ

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualOriginalApplication
