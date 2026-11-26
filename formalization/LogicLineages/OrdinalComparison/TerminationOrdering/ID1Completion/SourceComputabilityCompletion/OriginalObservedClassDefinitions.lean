module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalObservedClass
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open OriginalTransparentMinimum
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Every nonreflexive class hit explicitly checks equality of observer values.
Inputs remain seed, candidate, parameter. No native calibration is assumed. -/
def observed (O : Program 1) (P : Program 3) : Program 3 :=
  InternalAcceptance.conjunction P
    (InternalApplicationStepPeel.same
      (.composition O (fun _ : Fin 1 => .projection 1))
      (.composition O (fun _ : Fin 1 => .projection 0)))

def HitLaw (T : Program 2) (O : Program 1) (P : Program 3) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed out parameter mark : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph3 (reflexiveClassTest T (observed O P))
        InternalOriginalStepGuard.one seed out parameter).imp
      ((InternalApplicationCertificateConstructors.graph1 O mark out).iff
        (InternalApplicationCertificateConstructors.graph1 O mark seed))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalObservedClass
