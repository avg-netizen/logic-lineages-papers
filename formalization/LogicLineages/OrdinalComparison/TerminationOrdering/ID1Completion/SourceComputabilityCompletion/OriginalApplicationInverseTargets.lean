module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationValidityFoldDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ClaudeSupervisedCompletion.InverseGuardTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationInverseTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalParameterizedApplicationValidityFold
open InternalOriginalUniformDescentSelection (Data validity)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Accepted original application-fold validity internally forces the actual
codomain node and BOTH original child folds to accept. Child outputs are
obtained inside the calculus; no validity oracle or calibration is assumed. -/
def ActualValidatorApplicationInversion : Prop :=
  ∀ (body : Positive (Fin 1)) (node oldLeaf : Program 2)
    (alpha : Type) (Gamma : List (Formula alpha))
    (arrow d e fp ap fn arg parent parameter : OTerm alpha),
  Nonempty (Derivation body Gamma
    ((InternalApplicationValidityClosure.applicationConstructors
        arrow d e fp ap fn arg parent ⊓
      graph2 (validatorP node oldLeaf) InternalOriginalStepGuard.one parent parameter).imp
      (graph2 node InternalOriginalStepGuard.one e parameter ⊓
        (graph2 (validatorP node oldLeaf) InternalOriginalStepGuard.one fn parameter ⊓
          graph2 (validatorP node oldLeaf) InternalOriginalStepGuard.one arg parameter))))

/-- The SAME selected Data validates both actual application children and
the codomain. The raw child type tags are retained because the original
application constructor itself stores only the child payloads. -/
def ActualSourceApplicationInversion : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data)
    (alpha : Type) (Gamma : List (Formula alpha))
    (arrow d e fn arg parent parameter : OTerm alpha),
  Nonempty (Derivation body Gamma
    ((graph2 InternalListCodec.consCode arrow d e ⊓
      (graph1 InternalUnpair.left arrow fn ⊓
        (graph1 InternalUnpair.left d arg ⊓
          (graph4 application parent d e fn arg ⊓
            graph2 (validity data) InternalOriginalStepGuard.one parent parameter)))).imp
      (graph2 data.member InternalOriginalStepGuard.one e parameter ⊓
        (graph2 (validity data) InternalOriginalStepGuard.one fn parameter ⊓
          graph2 (validity data) InternalOriginalStepGuard.one arg parameter))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationInverseTargets
