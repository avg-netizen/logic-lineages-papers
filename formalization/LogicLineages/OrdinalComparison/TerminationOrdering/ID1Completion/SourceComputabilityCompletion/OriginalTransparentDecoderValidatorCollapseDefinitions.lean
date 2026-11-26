module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderSelectionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapse
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The SAME initially selected transparent tuple, before any runtime input. -/
def transparent (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :
    GlobalSourcePackage.Inputs :=
  OriginalTransparentDecoderSelection.transparentInputs H G W p

/-- Exactly ONE original variable-leaf refinement of that same tuple. -/
def refined (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :
    GlobalSourcePackage.Inputs :=
  OriginalVariableLeaves.refineInputs G (transparent p H G W)

/-- The unchanged accepted final pipeline. Neither its representative nor
its source/target/member programs are reselected for this bridge. -/
def selected (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :
    InternalOriginalUniformDescentSelection.Data :=
  OriginalLambdaTraversalSelection.finalData (refined p H G W)

/-- Equality of every internal output graph, with wholly arbitrary raw
packed value, original outer context, Encodable Gamma and arithmetic output.
This is an independent Derivation contract, not evaluation equality. -/
def GraphEquality (left right : Program 2) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out raw parameter : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph2 left out raw parameter).iff (graph2 right out raw parameter)))

/-- Local HT uses the actual framed validator with its original payload+1
fuel and constant-one auxiliary callbacks. The right side is q.oldTarget. -/
def TargetCollapse (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Prop :=
  GraphEquality
    (OriginalTransparentLambdaValidity.targetValidator (refined p H G W).base)
    (transparent p H G W).base.oldTarget

/-- Local HS retains BOTH normalized root callbacks at every node. In
particular the target callback supplies the original G guard missing from
the refined variable-source leaf. The right side is q.oldSource, not r.oldSource. -/
def SourceCollapse (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Prop :=
  GraphEquality
    (OriginalTransparentLambdaValidity.sourceValidator (refined p H G W).base)
    (transparent p H G W).base.oldSource

/-- Actual final target validity at the SAME selected D, not a replacement
relation or a newly chosen tuple. No canonical or transport premise is added. -/
def FinalTargetCollapse (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Prop :=
  GraphEquality
    (InternalOriginalUniformDescentSelection.targetValidity (selected p H G W))
    (transparent p H G W).base.oldTarget

/-- Actual final source validity at that identical D. The proof must remove
the actual HT conjunction internally; native source typing is not reflection. -/
def FinalSourceCollapse (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Prop :=
  GraphEquality
    (InternalOriginalUniformDescentSelection.validity (selected p H G W))
    (transparent p H G W).base.oldSource

/- SPECIFICATION ONLY. The four bridges use arbitrary Programs H/G/W and
arbitrary initial p. No native calibration, successful decoder run, typed
raw input, source-window closure, or transported acceptance is assumed.
They preserve the original packed-number/Encodable-Gamma distinction and
all existing fuel, normalization and final-selection ASTs. These contracts
assert neither internal canonical fixedness nor full internal I/C. -/
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapse
