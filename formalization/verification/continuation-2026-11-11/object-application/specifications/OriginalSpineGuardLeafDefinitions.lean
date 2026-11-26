module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSpineMeasureDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineGuardLeaf
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Keep the WHOLE original leaf as a factor and test only the original raw
endpoints with the existing bottom-spine observer. The original certificate
and separate symbolic parameter retain their positions and encodings. -/
def refined (oldStep : Program 4) : Program 4 :=
  InternalAcceptance.conjunction oldStep
    (PositiveGuard.spineGuard BottomSpineMeasure.measure)

/-- Literal existing guard acceptance, with all four original coordinates.
This conditional guard demands a flagged target and strict target-depth
decrease only when the source's actual bottom-spine flag is exactly one. -/
abbrev spineAccepted {alpha : Type}
    (source target certificate parameter : OTerm alpha) : Formula alpha :=
  graph4 (PositiveGuard.spineGuard BottomSpineMeasure.measure)
    InternalOriginalStepGuard.one source target certificate parameter

/-- Internal leaf consequence for arbitrary bodies, contexts and raw inputs.
This compositional supplier is separately discharged for the concrete refined
leaf; numerical calibration is not used as an internal inference rule. -/
def LeafHasSpineGuard (leaf : Program 4) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (source target certificate parameter : OTerm alpha),
  Nonempty (Derivation body Delta
    ((OriginalConstructorLeaf.accepted leaf source target certificate parameter).imp
      (spineAccepted source target certificate parameter)))

/-- Only the oldStep AST changes, once before any finite source context or
runtime Gamma is selected. Every other original input field stays literal. -/
def refineInputs (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
  { p with oldStep := refined p.oldStep }

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineGuardLeaf
