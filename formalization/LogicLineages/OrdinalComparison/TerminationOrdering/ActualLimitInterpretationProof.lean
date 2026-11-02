module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitInterpretationTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitInterpretationProof
open Source Source.SourceMarkedSyntax FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice FunctionalTupleBuilder SourceConstructorOperator SourceConstructorIteration

theorem rowFixed {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} (I : Input Symbol arity)
    (above : Symbol → Symbol → Prop) [DecidableRel above] (f : HeadIndex I) (τ : TypeIndex I) (P : World I) (a : Inputs I f P) :
    operatorRaw above (limit I above) f τ P a=(limit I above).val f τ P a :=
  congrArg (fun M : Constructors I => M.val f τ P a)
    (SourceConstructorIterationProof.actualFixedPoint Symbol inferInstance arity I above inferInstance)

theorem sourceBitEquations : ActualLimitInterpretationTargets.SourceBitEquations := by
  intro Symbol inst arity I above dec f τ P a Q
  have h := SourceConstructorOperatorProof.sourceBitEquations Symbol inst arity I above dec (limit I above) f τ P a Q
  rw [rowFixed] at h
  exact h

theorem fullTupleEquation : ActualLimitInterpretationTargets.FullTupleEquation := by
  intro Symbol inst arity I above dec f τ P a Q s v
  have h := SourceConstructorOperatorProof.fullTupleEquation Symbol inst arity I above dec (limit I above) f τ P a Q s v
  rw [rowFixed] at h
  exact h

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitInterpretationProof
