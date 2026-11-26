module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaRootProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaRebuildProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open OriginalLambdaConstructorGraphSyntaxProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalAcceptanceSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open InternalOriginalUniformDescentSelection (Data)
open OriginalLambdaTraversalInternal OriginalLambdaTraversalSelection
open OriginalTransparentLambdaFinal OriginalTransparentLambdaValidityInternal
open OriginalTransparentLambdaValidityInternalSourceSyntaxProof
open OriginalLambdaTraversalLambdaSelectorProof OriginalLambdaTraversalLambdaStateProof
open OriginalLambdaTraversalLambdaSourceProof OriginalLambdaTraversalLambdaRootProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Rebuilding with the original constructor preserves the actual parameter,
and exposes the SAME computed body through the traversal's own selectors. -/
theorem rebuiltFields (raw out d e child typ parameter bodyParameter : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversal.rawDomain d raw)))
    (hp : Nonempty (Derivation body Delta
      (graph2 OriginalLambdaTraversal.childParameter bodyParameter raw parameter)))
    (ha : Nonempty (Derivation body Delta (graph2 OriginalLambdaConstructor.arrow typ d e)))
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left e child)))
    (hc : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor out d e child))) :
    Nonempty (Derivation body Delta
      (LambdaFields out d e child parameter bodyParameter ⊓ graph1 InternalUnpair.left typ out)) := by
  have hf := OriginalLambdaConstructorGraphFieldsProof.constructorFields out d e child typ hc ht ha
  have htag := andLeft hf
  have htype := andLeft (andRight hf)
  have hdomain := andLeft (andRight (andRight (andRight hf)))
  have hbody := andRight (andRight (andRight (andRight hf)))
  let xs : Fin 1 → OTerm alpha := Fin.cons out Fin.elim0
  have he := unaryValue InternalListCodec.tailCode OriginalLambdaTraversal.rawType e typ xs
    (andLeft (andRight (InternalListCodecSupportProof.consDestruction typ d e ha))) htype
  have hb := binaryValue OriginalLambdaConstructor.bodyCode OriginalLambdaTraversal.rawCodomain
    (.projection 0) child e out xs hbody he (projectionValue 0 xs)
  have hparam := childParameterCongr raw out d parameter bodyParameter hd hdomain hp
  exact andIntro (andIntro htag (andIntro hdomain (andIntro he (andIntro hb hparam)))) htype

/-- Source validity is reconstructed at the SAME selected source and runtime
parameter. Original arrow/domain memberships come from the accepted parent;
the child source graph is the induction conclusion, not a semantic shortcut. -/
theorem sourceRebuild (rawData : Data) (window : Program 1)
    (raw out d e child childOut typ parameter bodyParameter : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (LambdaFields raw d e child parameter bodyParameter)))
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ raw)))
    (hs : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (leafData rawData window))
        (numeral 1) raw parameter)))
    (hb : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (leafData rawData window))
        (numeral 1) childOut bodyParameter)))
    (hbt : Nonempty (Derivation body Delta (graph1 InternalUnpair.left e childOut)))
    (hc : Nonempty (Derivation body Delta
      (graph3 OriginalLambdaConstructor.constructor out d e childOut))) :
    Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (leafData rawData window))
        (numeral 1) out parameter ⊓
        (LambdaFields out d e childOut parameter bodyParameter ⊓ graph1 InternalUnpair.left typ out))) := by
  let data := leafData rawData window
  have law := OriginalLambdaTraversalSelectionValidityProof.leafSourceLambda rawData window
  have hd := andLeft (andRight hf)
  have he := andLeft (andRight (andRight hf))
  have hp := andRight (andRight (andRight (andRight hf)))
  have hroot := andLeft (sourceAccepted data law raw parameter (andLeft hf) hs)
  have hfields := sourceFieldsAt data raw parameter typ d e ht hd he hroot
  have ha := andLeft (andRight (andRight (andRight hfields)))
  have hm := andRight (andRight (andRight (andRight hfields)))
  have rebuilt := rebuiltFields raw out d e childOut typ parameter bodyParameter hd hp ha hbt hc
  have hr := andLeft rebuilt
  have hrt := andRight rebuilt
  have hrd := andLeft (andRight hr)
  have hre := andLeft (andRight (andRight hr))
  have hrb := andLeft (andRight (andRight (andRight hr)))
  have hrp := andRight (andRight (andRight (andRight hr)))
  have rootOut := sourceIntro data out parameter typ d e
    (andIntro hrt (andIntro hrd
      (andIntro (andLeft (andRight (InternalListCodecSupportProof.consDestruction typ d e ha)))
        (andIntro ha hm))))
  have childOutFactors := finalChildFromSelectors
    (InternalOriginalUniformDescentSelection.validity data) out e childOut parameter bodyParameter
    hre hrb hrp hb
  exact andIntro (sourceFromFactors data law out parameter (andLeft hr)
    (andIntro rootOut childOutFactors)) rebuilt

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaRebuildProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaRebuildProof
