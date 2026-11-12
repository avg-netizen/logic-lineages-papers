module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableErasureCertificateDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalErasureCertificateContinuation
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalComputabilityApplication InternalAccessibilityRules
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion OriginalRawObjectTransport OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- A literal original variable Object constructor, used only to describe
an output. This does not replace any selected source or target Program. -/
def variableObjectCode : Program 3 :=
  pairOf (.projection 1)
    (pairOf (.projection 0) (.composition variableConstructor (fun _ : Fin 1 => .projection 2)))

/-- An arbitrary original variable in an actual cons context. The variable
index is not restricted to zero, and the erased type need not be its type. -/
def Shape {alpha : Type} (tau : Ty)
    (source gamma extended packed raw domain index : OTerm alpha) : Formula alpha :=
  graph2 InternalListCodec.consCode extended domain gamma ⊓
    (graph1 variableConstructor raw index ⊓
      (graph2 InternalPairing.pairing packed
          (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) raw ⊓
        graph2 InternalPairing.pairing source extended packed))

def Premise (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    {alpha : Type} (context : Nat) (tau : Ty)
    (source target witness gamma extended packed raw domain index : OTerm alpha) : Formula alpha :=
  let r := OriginalFinalGuardedRank.refined p H G W
  let f := OriginalLambdaTraversalSelection.finalInputs r
  graph1 f.window (numeral 1) (numeral context) ⊓
    (typed (GlobalSourcePackage.computability f) tau (numeral context) source ⊓
      (Shape tau source gamma extended packed raw domain index ⊓
        certificate (GlobalSourcePackage.source f) false context source target witness))

/-- The original successor and rank drop are determined for EVERY original
variable certificate, independently of which context entry is erased. -/
def EndpointResult {alpha : Type} (tau : Ty)
    (source target extended : OTerm alpha) : Formula alpha :=
  ComputabilityLeast.bottomGraph target
    (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) extended ⊓
      OriginalVariableErasureCertificate.OriginalRankDrop source target

/-- In the surviving-variable branch, erasure maps index succ i to i.
Both output shapes and their ranks are conclusions. The actual original
certificate, not a supplied target-bottom shape, starts the argument. -/
def SurvivorResult {alpha : Type} (tau : Ty)
    (source target gamma extended index erasedSource erasedTarget : OTerm alpha) : Formula alpha :=
  EndpointResult tau source target extended ⊓
    (graph3 variableObjectCode erasedSource
       (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) gamma index ⊓
      (ComputabilityLeast.bottomGraph erasedTarget
         (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) gamma ⊓
        OriginalVariableErasureCertificate.OriginalRankDrop erasedSource erasedTarget))

/- This packet supplies the non-collapsing variable endpoint branch. It does
not construct a transformed positive certificate, prove general canonical
cancellation, or claim internal substitution/I/C or the closed lemma. -/
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalErasureCertificateContinuation
