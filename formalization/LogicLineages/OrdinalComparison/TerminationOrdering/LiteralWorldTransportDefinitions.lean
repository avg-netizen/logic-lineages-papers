module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualStrictMarkProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.LiteralWorldTransport
open Source Source.SourceMarkedSyntax Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment CoherentConstructorLattice ConfinedStructuralInterpretation TypedObservationAccess LambdaObservationMatching

def weakenSource {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {P Q : World I} (h : Extends P Q) {τ : Ty} (q : ConfinedTerm I (portTypes P.val++I.context) τ) :
    ConfinedTerm I (portTypes Q.val++I.context) τ :=
  StructuralRenaming.renameSource (LiteralVariableValue.extendVariables I.context Q.val P.val h) q

end LogicLineages.OrdinalComparison.TerminationOrdering.LiteralWorldTransport
