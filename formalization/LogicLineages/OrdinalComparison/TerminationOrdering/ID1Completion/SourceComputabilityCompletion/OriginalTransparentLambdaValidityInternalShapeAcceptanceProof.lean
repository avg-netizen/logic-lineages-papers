module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalSelectorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalShapeSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBooleanProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalShapeAcceptanceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalTransparentLambdaValidity OriginalTransparentLambdaValidityInternal
open OriginalTransparentLambdaValidityInternalSelectorProof OriginalTransparentLambdaValidityInternalShapeSyntaxProof
open OriginalTransparentLambdaValidityInternalBooleanProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem shapeAtFields (raw parameter typ d e : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (shapeFields raw typ d e))) :
    Nonempty (Derivation body Gamma (graph2 lambdaShape (numeral 1) raw parameter)) := by
  let xs : Fin 2 → OTerm alpha := ![raw,parameter]
  have ht := resultTypeValue typ raw parameter (andLeft hf)
  have hd : Nonempty (Derivation body Gamma (graph2 domain d raw parameter)) :=
    unaryValue OriginalLambdaConstructor.domain (.projection 0) d raw xs
      (andLeft (andRight hf)) (projectionValue 0 xs)
  have he : Nonempty (Derivation body Gamma (graph2 codomain e raw parameter)) :=
    unaryValue InternalListCodec.tailCode resultType e typ xs
      (andLeft (andRight (andRight hf))) ht
  exact sameAccept resultType (consOf domain codomain) typ xs ht
    (binaryValue InternalListCodec.consCode domain codomain typ d e xs
      (andRight (andRight (andRight hf))) hd he)

theorem shapeValue (raw parameter : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (LambdaShape raw))) :
    Nonempty (Derivation body Gamma (graph2 lambdaShape (numeral 1) raw parameter)) := by
  apply shapeCases raw _ hf
  intro beta j Delta typ d e hj hf'
  simp only [graph2Rename,numeral,sucRelabel,zRelabel]
  exact shapeAtFields (raw.relabel j) (parameter.relabel j) typ d e hf'

theorem shapeRecover (raw parameter : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (graph2 lambdaShape (numeral 1) raw parameter))) :
    Nonempty (Derivation body Gamma (LambdaShape raw)) := by
  apply queryCases ![resultType,domain,codomain] (Fin.cons raw (Fin.cons parameter Fin.elim0)) _
  intro beta j ys Delta hj hq
  have hs' := renameInto hs j Delta hj
  simp only [graph2Rename,numeral,sucRelabel,zRelabel] at hs'
  simp only [consTermRename,emptyRename] at hq
  simp only [shapeRename]
  let xs : Fin 2 → OTerm beta := Fin.cons (raw.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
  have qt : Nonempty (Derivation body Delta (graph2 resultType (ys 0) (raw.relabel j) (parameter.relabel j))) := hq 0
  have qd : Nonempty (Derivation body Delta (graph2 domain (ys 1) (raw.relabel j) (parameter.relabel j))) := hq 1
  have qe : Nonempty (Derivation body Delta (graph2 codomain (ys 2) (raw.relabel j) (parameter.relabel j))) := hq 2
  have ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left (ys 0) (raw.relabel j))) :=
    unaryRecover InternalUnpair.left (.projection 0) (ys 0) (raw.relabel j) xs
      qt (projectionValue 0 xs)
  have hd : Nonempty (Derivation body Delta
      (graph1 OriginalLambdaConstructor.domain (ys 1) (raw.relabel j))) :=
    unaryRecover OriginalLambdaConstructor.domain (.projection 0) (ys 1) (raw.relabel j) xs
      qd (projectionValue 0 xs)
  have he := unaryRecover InternalListCodec.tailCode resultType (ys 2) (ys 0) xs qe qt
  have ha := binaryRecover InternalListCodec.consCode domain codomain (ys 0) (ys 1) (ys 2) xs
    (sameLeftRecover resultType (consOf domain codomain) (ys 0) xs hs' qt) qd qe
  exact shapeIntro (raw.relabel j) (ys 0) (ys 1) (ys 2)
    (andIntro ht (andIntro hd (andIntro he ha)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalShapeAcceptanceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalShapeAcceptanceProof
