module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldInductionTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveDeadCurrentTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalSparseFieldInductionTargets (malformed)
open NumberedWindowInternalSparsePositiveFold (finish)
open NumberedWindowInternalSparsePositiveOutputTargets (args4)

/-- A genuine positive raw input lacking its leading polynomial-cons
preimage causes the actual chosen-fuel finish to return zero. This is
the leading-cell gap, not a meta-level assertion about all parse failure. -/
def OpenMalformedFinishZero : Prop :=
  ∀ (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3) (α : Type)
    (ctx ty current certificate : OTerm α),
    Nonempty (Derivation body [] ((malformed certificate).imp
      (programGraph (finish raw least) z (args4 ctx ty current certificate))))

/-- The original encoded none0 current is absorbing through the entire
ordered certificate at its own chosen raw-code fuel. The certificate
and context/type terms are arbitrary; no parse or typing assumption. -/
def OpenNoCurrentFinishZero : Prop :=
  ∀ (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3) (α : Type)
    (ctx ty certificate : OTerm α),
    Nonempty (Derivation body []
      (programGraph (finish raw least) z (args4 ctx ty z certificate)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveDeadCurrentTargets
