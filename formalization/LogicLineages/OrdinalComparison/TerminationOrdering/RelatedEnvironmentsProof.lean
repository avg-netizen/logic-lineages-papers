module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RelatedEnvironmentsTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RelatedEnvironmentsProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open Source.SourcePortContexts FiniteObservationBits TypedValueEnvironment ActualValueLogicalRelation
open RelatedEnvironments LambdaObservationMatching

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem weakening : RelatedEnvironmentsTargets.Weakening := by
  intro Symbol inst arity I above Gamma P Q h rho s hr tau v
  exact LogicalRelationWorldsProof.relatedWeakening Symbol inst arity I above tau P Q h
    (rho v) (s v) (hr v)

theorem extension : RelatedEnvironmentsTargets.Extension := by
  intro Symbol inst arity I above Gamma P rho s sigma a q hr ha tau v
  cases v with
  | here => exact ha
  | there v => exact hr v

theorem freshOpening : RelatedEnvironmentsTargets.FreshOpening := by
  intro Symbol inst arity I above Gamma P rho s sigma upsilon i h hr tau v
  let Q : World I := ⟨(i,sigma)::P.val,h.2.1⟩
  let ext : Extends P Q := fun p hp => List.mem_cons_of_mem _ hp
  cases v with
  | here =>
    exact LogicalRelationWorldsProof.literalVariableRelated Symbol inst arity I above sigma Q Variable.here
  | there v =>
    have hv := LogicalRelationWorldsProof.relatedWeakening Symbol inst arity I above tau P Q ext
      (rho v) (s v) (hr v)
    have rename_eq : @Eq (Renaming (portTypes P.val++I.context) (sigma::(portTypes P.val++I.context)))
        (LogicalRelationWorlds.portRename ext) (Renaming.weaken _ sigma) := by
      funext tau v
      exact LiteralWorldTransportProof.consPortTransport Symbol inst arity I P sigma i h.2.1 tau v
    unfold futureSyntax at hv
    change Related I above tau Q (RecursiveNaturalDomains.weaken ext (rho v))
      (renameTerm (s v) (LogicalRelationWorlds.portRename ext)) at hv
    rw [rename_eq] at hv
    exact hv

end LogicLineages.OrdinalComparison.TerminationOrdering.RelatedEnvironmentsProof
