module

public import LogicLineages.PersistentMarking.NumberedWindowScalarAlgorithm
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSettingsGrammarGuardDefinitions
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)

/-- Physical standard scratch membership in the actual full grammar type
list, at the original open input; no window-list value is substituted. -/
def grammarTypeAt (s : Settings) : Program 1 :=
  .composition scratchMember ![literal 1 (Encodable.encode s.types),.projection 0]

/-- Deliberate reselection of the type-guard AST. Its left conjunct is
the same supplied T. Its right conjunct is a literal grammar membership
report, not a new predicate known only by numerical equivalence. -/
def refitGuard (s : Settings) (T : Program 1) : Program 1 :=
  conjunction T (grammarTypeAt s)

end LogicLineages.PersistentMarking.NumberedWindowInternalSettingsGrammarGuardDefinitions
