module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplication
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data validity)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The original requested function is selected-typed; the raw argument needs
only its original source validity and domain field. The original arrow,
codomain membership, active window and symbolic parameter remain literal.
No function/argument full-fold fixedness or sidecar fixedness is supplied. -/
def InputPremises {alpha : Type} (data : Data) (window : Program 1)
    (arrow d e function argument parameter : OTerm alpha) : Formula alpha :=
  OriginalFunctionNeutrality.windowGraph window function parameter ⊓
    (graph2 InternalListCodec.consCode arrow d e ⊓
      (graph2 data.member InternalOriginalStepGuard.one e parameter ⊓
        (InternalOriginalUniformApplicationTyping.typedGraph data function arrow parameter ⊓
          (graph2 (validity data) InternalOriginalStepGuard.one argument parameter ⊓
            graph1 InternalUnpair.left d argument))))

/-- The requested function remains literal; the argument's actual full-fold
output is bound internally by the final consumer and is retained explicitly.
The constructor is the original whole-child application Program. -/
def Recovered {alpha : Type} (data : Data)
    (d e function argument out argumentOut parameter : OTerm alpha) : Formula alpha :=
  InternalParameterizedCanonicalResultFold.foldGraph data argumentOut argument parameter ⊓
    graph4 application out d e function argumentOut

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplication
