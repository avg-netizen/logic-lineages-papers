module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectRankTransportDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableErasureCertificate
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalComputabilityApplication InternalAccessibilityRules
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion OriginalRawObjectTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Literal original constructor graphs identify the variable at de Bruijn
index zero in the genuine cons context. Both the packed outer type and the
erased context entry are the requested original type number. No decoder,
target shape, equality or rank is supplied by this shape condition. -/
def TopVariableShape {alpha : Type} (tau : Ty)
    (source gamma extended packed raw : OTerm alpha) : Formula alpha :=
  graph2 InternalListCodec.consCode extended
      (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) gamma ⊓
    (graph1 OriginalRawSyntaxTransport.variableConstructor raw (numeral 0) ⊓
      (graph2 InternalPairing.pairing packed
          (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) raw ⊓
        graph2 InternalPairing.pairing source extended packed))

/-- The actual original positive certificate and original input typing use
the SAME final source/computability tuple as the accepted canonical Object
and rank contracts. The outer active window is explicit. The successor is
unrestricted: its bottom shape must follow from the original variable
certificate law, not from an extra premise. -/
def Premise (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    {alpha : Type} (context : Nat) (tau : Ty)
    (source target witness gamma extended packed raw : OTerm alpha) : Formula alpha :=
  let r := OriginalFinalGuardedRank.refined p H G W
  let f := OriginalLambdaTraversalSelection.finalInputs r
  graph1 f.window (numeral 1) (numeral context) ⊓
    (typed (GlobalSourcePackage.computability f) tau (numeral context) source ⊓
      (TopVariableShape tau source gamma extended packed raw ⊓
        certificate (GlobalSourcePackage.source f) false context source target witness))

/-- Strict decrease concerns the ORIGINAL certificate endpoints. The two
actual rank graphs are conclusions, with the literal values one and zero;
there is no supplied rank graph and no rank defined from an erasure delta. -/
def OriginalRankDrop {alpha : Type} (source target : OTerm alpha) : Formula alpha :=
  graph1 variableRankObjectRaw (numeral 1) source ⊓
    (graph1 variableRankObjectRaw (numeral 0) target ⊓
      InternalLessThan.strictLess (numeral 0) (numeral 1))

/-- The certificate determines the original target bottom at the extended
Gamma. The literal raw erasures are both the same original bottom Object
at the tail Gamma. All three bottom graphs, their equality and the strict
rank decrease between the original endpoints are derived conclusions. -/
def RawResult {alpha : Type} (tau : Ty)
    (source target gamma extended erasedSource erasedTarget : OTerm alpha) : Formula alpha :=
  ComputabilityLeast.bottomGraph target
      (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) extended ⊓
    (ComputabilityLeast.bottomGraph erasedSource
        (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) gamma ⊓
      (ComputabilityLeast.bottomGraph erasedTarget
          (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) gamma ⊓
        (equal erasedSource erasedTarget ⊓ OriginalRankDrop source target)))

/-- Independent internal variable-collapse branch of original positive
erasure transport. Both transformed endpoints are actual eraseObjectRaw
outputs. No target-bottom, output-equality, rank, transformed typing or
canonical fixedness premise replaces the required certificate argument. -/
def RawCollapseLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (context : Nat) (tau : Ty)
    (source target witness gamma extended packed raw erasedSource erasedTarget : OTerm alpha),
  Nonempty (Derivation body Delta
    ((Premise p H G W context tau source target witness gamma extended packed raw ⊓
      (graph1 eraseObjectRaw erasedSource source ⊓
        graph1 eraseObjectRaw erasedTarget target)).imp
      (RawResult tau source target gamma extended erasedSource erasedTarget)))

/-- The two literal raw erasures are then fed to the SAME actual final K,
at the SAME original outer context. Their actual K outputs coincide, while
the strict drop remains between the original certificate endpoints. This
uses neither canonical fixedness of a raw erasure nor an alternative fold. -/
def CanonicalCollapseLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) : Prop :=
  let r := OriginalFinalGuardedRank.refined p H G W
  let K := OriginalFinalVariableObject.canonicalObjectProgram r
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (context : Nat) (tau : Ty)
    (source target witness gamma extended packed raw
      erasedSource erasedTarget canonicalSource canonicalTarget : OTerm alpha),
  Nonempty (Derivation body Delta
    ((Premise p H G W context tau source target witness gamma extended packed raw ⊓
      (graph1 eraseObjectRaw erasedSource source ⊓
        (graph1 eraseObjectRaw erasedTarget target ⊓
          (graph2 K canonicalSource (numeral context) erasedSource ⊓
            graph2 K canonicalTarget (numeral context) erasedTarget)))).imp
      (RawResult tau source target gamma extended erasedSource erasedTarget ⊓
        equal canonicalSource canonicalTarget)))

/- These contracts cover only the matched top-variable certificate branch.
They do not assert a general positive-path transformer, the full erasure
dichotomy, shifted certificate transport, internal substitution/I/C or the
closed all-term accessibility endpoint. No native calibration is reflected
into an internal Derivation. -/
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableErasureCertificate
