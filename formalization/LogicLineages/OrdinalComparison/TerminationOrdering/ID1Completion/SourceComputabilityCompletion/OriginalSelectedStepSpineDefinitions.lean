module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineGuardLeafDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpine
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open OriginalSpineGuardLeaf
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The actual original peel-and-repeat checker at an arbitrary endpoint
Program implies the existing spine guard at its UNCHANGED raw inputs. No
normalized state, child witness, original path decomposition or mark output
is provided by the caller. The symbolic parameter is never iteration fuel. -/
def SelectedHasSpineGuard (endpoint : Program 6) (oldStep : Program 4) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (source target certificate parameter : OTerm alpha),
  Nonempty (Derivation body Delta
    ((InternalParameterizedApplicationStepChecker.checkerGraph endpoint oldStep
        InternalOriginalStepGuard.one source target certificate parameter).imp
      (spineAccepted source target certificate parameter)))

/-- Retain the complete original guarded raw-step acceptance, including its
source/target validity and common outer type. The conclusion concerns those
same raw endpoints and their same certificate and parameter. This is not an
Object/source positive certificate or a canonical quotient-edge statement. -/
def RawStepHasSpineGuard (data : Data) (oldStep : Program 4) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (source target certificate parameter : OTerm alpha),
  Nonempty (Derivation body Delta
    ((UniformCertificateCompletion.stepAccepted data oldStep
        source target certificate parameter).imp
      (spineAccepted source target certificate parameter)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpine
