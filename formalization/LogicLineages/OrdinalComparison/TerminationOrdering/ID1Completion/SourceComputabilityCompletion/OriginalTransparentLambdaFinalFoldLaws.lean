module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalFoldDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalFoldLaws
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationValidityClosure
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Auxiliary all-output graph compatibility required of the actual callbacks.
Instantiations must prove these laws inside the calculus, not by native equality. -/
def LeafLaw (body : Positive (Fin 1)) (guard leaf valid : Program 2) : Prop :=
  ∀ (α : Type) (Gamma : List (Formula α)) (out input parameter : OrdinaryArithmetic.Term α),
    Nonempty (Derivation body Gamma (graph2
      (InternalParameterizedApplicationResultStack.openGuardP guard)
      OrdinaryArithmetic.zeroTerm input parameter)) →
    Nonempty (Derivation body Gamma (graph2 leaf out input parameter)) →
    Nonempty (Derivation body Gamma (graph2 valid out input parameter))

def ApplicationLaw (body : Positive (Fin 1)) (guard valid : Program 2)
    (combine : Program 5) : Prop :=
  ∀ (α : Type) (Gamma : List (Formula α))
    (arrow d e fp ap fn arg parent functionOut argumentOut out parameter : OrdinaryArithmetic.Term α),
    Nonempty (Derivation body Gamma
      (applicationConstructors arrow d e fp ap fn arg parent)) →
    Nonempty (Derivation body Gamma
      (graph2 guard InternalOriginalStepGuard.one parent parameter)) →
    Nonempty (Derivation body Gamma (graph2 valid functionOut fn parameter)) →
    Nonempty (Derivation body Gamma (graph2 valid argumentOut arg parameter)) →
    Nonempty (Derivation body Gamma
      (programGraph combine out (Fin.cons d (Fin.cons e (Fin.cons functionOut
        (Fin.cons argumentOut (Fin.cons parameter Fin.elim0))))))) →
    Nonempty (Derivation body Gamma (graph2 valid out parent parameter))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalFoldLaws
