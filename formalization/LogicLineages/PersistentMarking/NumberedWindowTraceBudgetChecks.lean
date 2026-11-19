import LogicLineages.PersistentMarking.NumberedWindowTraceConsProof
import LogicLineages.PersistentMarking.NumberedWindowTraceContextsProof
import LogicLineages.PersistentMarking.NumberedWindowOrdinaryDomainProof
import LogicLineages.PersistentMarking.NumberedWindowReservedMarkWindowProof

namespace LogicLineages.PersistentMarking.NumberedWindowTraceBudgetChecks
open NumberedWindowTraceBudgetTargets

theorem exact_LiteralTermVertices : LiteralTermVertices :=
  NumberedWindowTraceJoinProof.termVertices

theorem exact_LiteralArgsVertices : LiteralArgsVertices :=
  NumberedWindowTraceJoinProof.listVertices

theorem exact_JoinTermTraces : JoinTermTraces :=
  NumberedWindowTraceJoinProof.termJoin

theorem exact_JoinArgsTraces : JoinArgsTraces :=
  NumberedWindowTraceJoinProof.argsJoin

theorem exact_LiftTypedLambda : LiftTypedLambda :=
  NumberedWindowTraceContextsProof.lambda

theorem exact_LiftTypedAuxFunction : LiftTypedAuxFunction :=
  NumberedWindowTraceContextsProof.auxiliaryFn

theorem exact_WindowPathAsRawTrace : WindowPathAsRawTrace :=
  NumberedWindowTraceContextsProof.fromWindowPath

theorem exact_ConsTypedTrace : ConsTypedTrace :=
  NumberedWindowTraceConsProof.cons

theorem exact_LiftTypedOrdinaryBase : LiftTypedOrdinaryBase :=
  NumberedWindowTraceContextsProof.ordinaryBase

theorem exact_OrdinaryTrDomain : OrdinaryTrDomain :=
  NumberedWindowOrdinaryDomainProof.termDomain

theorem exact_OrdinaryTrArgsDomain : OrdinaryTrArgsDomain :=
  NumberedWindowOrdinaryDomainProof.listDomain

theorem exact_UniqueOrdinaryRealization : UniqueOrdinaryRealization :=
  fun q Q h => (NumberedWindowOrdinaryQuoteProof.term q Q h).2

theorem exact_UniqueOrdinaryArgsRealization : UniqueOrdinaryArgsRealization :=
  fun qs As h => (NumberedWindowOrdinaryQuoteProof.list qs As h).2

theorem exact_OneReservedMarkStep : OneReservedMarkStep :=
  NumberedWindowReservedMarkWindowProof.reserved

#print axioms exact_LiteralTermVertices
#print axioms exact_LiteralArgsVertices
#print axioms exact_JoinTermTraces
#print axioms exact_JoinArgsTraces
#print axioms exact_LiftTypedLambda
#print axioms exact_LiftTypedAuxFunction
#print axioms exact_WindowPathAsRawTrace
#print axioms exact_ConsTypedTrace
#print axioms exact_LiftTypedOrdinaryBase
#print axioms exact_OrdinaryTrDomain
#print axioms exact_OrdinaryTrArgsDomain
#print axioms exact_UniqueOrdinaryRealization
#print axioms exact_UniqueOrdinaryArgsRealization
#print axioms exact_OneReservedMarkStep

end LogicLineages.PersistentMarking.NumberedWindowTraceBudgetChecks
