module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaBodyObjectMembershipProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectTypedTransportSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalBodyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalTransitionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaBodyObjectSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalAcceptanceSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalOriginalUniformDescentSelection (validity selectedTyped)
open InternalOriginalUniformDescentSelectionInternalProof (typedRecover typedAccept)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalLambdaBodyObject
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Proof-local simultaneous queries bind exactly the nine exposed runtime
coordinates. Each selector receives the supplied original Object in slot 0. -/
def extendedGamma : Program 1 := consOf domainCode InternalUnpair.left
def outerParameter (context : Nat) : Program 1 :=
  pairOf (constant 1 context) InternalUnpair.left
def extendedParameter (context : Nat) : Program 1 :=
  pairOf (constant 1 context) extendedGamma
def runtimeQueries (context : Nat) : Fin 9 → Program 1 :=
  ![InternalUnpair.left,InternalUnpair.right,domainCode,codomainCode,packedBody,
    outerParameter context,extendedGamma,extendedParameter context,bodyObject]

/-- Literal context extension is exactly the parameter program used by the
original lambda traversal. The parent domain and both Gamma codes stay symbolic. -/
theorem childParameterAtPairs (raw d c gamma parameter extended bodyParameter : OTerm alpha)
    (hd : Nonempty (Derivation body Delta
      (graph1 OriginalLambdaTraversal.rawDomain d raw)))
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter c gamma)))
    (he : Nonempty (Derivation body Delta
      (graph2 InternalListCodec.consCode extended d gamma)))
    (hb : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing bodyParameter c extended))) :
    Nonempty (Derivation body Delta
      (graph2 OriginalLambdaTraversal.childParameter bodyParameter raw parameter)) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
  let domain : Program 2 :=
    .composition OriginalLambdaTraversal.rawDomain (fun _ : Fin 1 => .projection 0)
  have hc := unaryValue InternalUnpair.left (.projection 1) c parameter xs
    (pairLeft parameter c gamma hp) (projectionValue 1 xs)
  have hg := unaryValue InternalUnpair.right (.projection 1) gamma parameter xs
    (pairRight parameter c gamma hp) (projectionValue 1 xs)
  have hdomain := unaryValue OriginalLambdaTraversal.rawDomain (.projection 0) d raw xs
    hd (projectionValue 0 xs)
  have hcons := binaryValue InternalListCodec.consCode domain (rightOf (.projection 1))
    extended d gamma xs he hdomain hg
  exact binaryValue InternalPairing.pairing (leftOf (.projection 1))
    (consOf domain (rightOf (.projection 1))) bodyParameter c extended xs hb hc hcons

theorem windowAtParameter (window : Program 1) (c gamma parameter input : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (graph1 window (numeral 1) c)))
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter c gamma))) :
    Nonempty (Derivation body Delta
      (OriginalFunctionNeutrality.windowGraph window input parameter)) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
  have hc := unaryValue InternalUnpair.left (.projection 1) c parameter xs
    (pairLeft parameter c gamma hp) (projectionValue 1 xs)
  exact unaryValue window (leftOf (.projection 1)) (numeral 1) c xs hw hc

/-- All original constructor and context fields use the same simultaneous
outputs; composition elimination prevents independently chosen body coordinates. -/
theorem fieldsFromQueries (context : Nat) (input : OTerm alpha)
    (ys : Fin 9 → OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 lambdaTag (numeral 1) input)))
    (hs : ∀ i, Nonempty (Derivation body Delta
      (programGraph (runtimeQueries context i) (ys i) (Fin.cons input Fin.elim0)))) :
    Nonempty (Derivation body Delta
      (OriginalContextExtension.Recovered (numeral context) (ys 2) input (ys 4)
        (ys 0) (ys 1) (ys 5) (ys 6) (ys 7) (ys 8) ⊓
       (OriginalLambdaTraversalInternal.LambdaFields
          (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 7) ⊓
        (graph1 codomainCode (ys 3) input ⊓ graph1 bodyObject (ys 8) input)))) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons input Fin.elim0
  have ho := reconstructPair input (ys 0) (ys 1) (hs 0) (hs 1)
  have he := binaryRecover InternalListCodec.consCode domainCode InternalUnpair.left
    (ys 6) (ys 2) (ys 0) xs (hs 6) (hs 2) (hs 0)
  have hp := binaryRecover InternalPairing.pairing (constant 1 context) InternalUnpair.left
    (ys 5) (numeral context) (ys 0) xs (hs 5) (constantValue context xs) (hs 0)
  have hbp := binaryRecover InternalPairing.pairing (constant 1 context) extendedGamma
    (ys 7) (numeral context) (ys 6) xs (hs 7) (constantValue context xs) (hs 6)
  have hbo := binaryRecover InternalPairing.pairing extendedGamma packedBody
    (ys 8) (ys 6) (ys 4) xs (hs 8) (hs 6) (hs 4)
  have htag := unaryRecover OriginalLambdaConstructor.tag InternalUnpair.right
    (numeral 1) (ys 1) xs ht (hs 1)
  have hd := unaryRecover OriginalLambdaConstructor.domain InternalUnpair.right
    (ys 2) (ys 1) xs (hs 2) (hs 1)
  have hc := unaryRecover OriginalLambdaTraversal.rawCodomain InternalUnpair.right
    (ys 3) (ys 1) xs (hs 3) (hs 1)
  have hb := unaryRecover OriginalLambdaTraversal.rawBody InternalUnpair.right
    (ys 4) (ys 1) xs (hs 4) (hs 1)
  have hchild := childParameterAtPairs (ys 1) (ys 2) (numeral context)
    (ys 0) (ys 5) (ys 6) (ys 7) hd hp he hbp
  exact andIntro (andIntro ho (andIntro he (andIntro hp (andIntro hbp hbo))))
    (andIntro (andIntro htag (andIntro hd (andIntro hc (andIntro hb hchild))))
      (andIntro (hs 3) (hs 8)))

/-- Actual parent typing factors into its final source/type/fixedness. The
accepted SAME-final lambda law gives the actual child's source and fixedness;
the original universe checker's root guard independently supplies membership. -/
theorem recoveredAtFields (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (context : Nat)
    (typ input gamma raw d e bodyRaw parameter extended bodyParameter childObject : OTerm alpha)
    (hinput : Nonempty (Derivation body Delta (Premise p H G W context typ input)))
    (hctx : Nonempty (Derivation body Delta
      (OriginalContextExtension.Recovered (numeral context) d input bodyRaw
        gamma raw parameter extended bodyParameter childObject)))
    (hlambda : Nonempty (Derivation body Delta
      (OriginalLambdaTraversalInternal.LambdaFields raw d e bodyRaw parameter bodyParameter)))
    (hcodomain : Nonempty (Derivation body Delta (graph1 codomainCode e input)))
    (hobject : Nonempty (Derivation body Delta (graph1 bodyObject childObject input))) :
    Nonempty (Derivation body Delta
      (Recovered p H G W context typ input gamma raw d e bodyRaw
        parameter extended bodyParameter childObject)) := by
  let s := OriginalRankGuardedRepresentative.guardedInputs H G W p
  let r := refined p H G W
  let D := finalData p H G W
  have hw := andLeft hinput
  have hp := andLeft hctx
  have hparameter := andLeft (andRight (andRight hctx))
  have hbodyParameter := andLeft (andRight (andRight (andRight hctx)))
  have hbodyObject := andRight (andRight (andRight (andRight hctx)))
  have htyped := OriginalCanonicalizedObjectTypedTransportSupportProof.outerRecover
    s H G W context typ input gamma raw parameter hw (andLeft (andRight hinput)) hp hparameter
  have hf := typedRecover D.oldRepresentative (validity D) D.member raw typ parameter htyped
  have hsource := andLeft (andRight hf)
  have htype := andLeft (andRight (andRight hf))
  have hfixed := andRight (andRight (andRight hf))
  have hwindow := windowAtParameter (finalInputs p H G W).window
    (numeral context) gamma parameter raw hw hparameter
  have hchild := OriginalLambdaTraversalFinalBodyProof.bodyAtType r
    (OriginalLambdaTraversalFinalTransitionProof.actualOriginalLambdaTraversalFinalTransition r)
    raw d e bodyRaw typ parameter bodyParameter hwindow hlambda hsource htype hfixed
  have hmember := OriginalLambdaBodyObjectMembershipProof.selectedMemberFromSource
    s H G W bodyRaw e bodyParameter (numeral context) extended hbodyParameter
    (andLeft (andRight hchild)) (andLeft hchild)
  have hfactors := andIntro hmember hchild
  have hchildTyped := typedAccept D.oldRepresentative (validity D) D.member
    bodyRaw e bodyParameter hfactors
  have houter := OriginalCanonicalizedObjectTypedTransportSupportProof.outerAccept
    s H G W context e childObject extended bodyRaw bodyParameter hw
    hbodyObject hbodyParameter hchildTyped
  have hconstructor := OriginalLambdaTraversalFinalSourceProof.finalSourceConstructor
    r raw d e bodyRaw typ parameter bodyParameter hlambda htype hsource
  have hfields := OriginalLambdaConstructorGraphFieldsProof.constructorFields
    raw d e bodyRaw typ (andRight hconstructor) (andLeft (andRight hchild))
    (andLeft hconstructor)
  exact andIntro hctx (andIntro hfields (andIntro (andRight hconstructor)
    (andIntro hlambda (andIntro hcodomain (andIntro hobject
      (andIntro hfactors (andIntro hchildTyped houter)))))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaBodyObjectSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaBodyObjectSupportProof
