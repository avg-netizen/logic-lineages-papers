module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalSourceSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalShapeAcceptanceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalSourceCheckProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalTransparentLambdaValidity OriginalTransparentLambdaValidityInternal
open OriginalTransparentLambdaValidityInternalSourceSyntaxProof OriginalTransparentLambdaValidityInternalShapeSyntaxProof
open OriginalTransparentLambdaValidityInternalShapeAcceptanceProof OriginalTransparentLambdaValidityInternalSelectorProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceConjunctionProof InternalGraphCompositionFunctionalityProof
open OriginalHereditaryValidityInternalNodeSupportProof (exactAccept exactRecover)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalOriginalUniformDescentSelection (Data)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Literal abbreviation for the existing sourceRoot lambda branch. -/
def sourceCheck (data : Data) : Program 2 :=
  InternalAcceptance.conjunction lambdaShape
    (InternalAcceptance.conjunction
      (OriginalHereditaryValidity.exactOne (.composition data.member ![resultType,.projection 1]))
      (OriginalHereditaryValidity.exactOne (.composition data.member ![domain,.projection 1])))

theorem sourceCheckAtFields (data : Data) (raw parameter typ d e : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (sourceFields data raw parameter typ d e))) :
    Nonempty (Derivation body Gamma (graph2 (sourceCheck data) (numeral 1) raw parameter)) := by
  let xs : Fin 2 → OTerm alpha := ![raw,parameter]
  have ht := resultTypeValue typ raw parameter (andLeft hf)
  have hd : Nonempty (Derivation body Gamma (graph2 domain d raw parameter)) :=
    unaryValue OriginalLambdaConstructor.domain (.projection 0) d raw xs
      (andLeft (andRight hf)) (projectionValue 0 xs)
  have hshape := shapeAtFields raw parameter typ d e
    (andIntro (andLeft hf) (andIntro (andLeft (andRight hf))
      (andIntro (andLeft (andRight (andRight hf))) (andLeft (andRight (andRight (andRight hf)))))))
  have hm := andRight (andRight (andRight (andRight hf)))
  exact conjunctionAccept _ _ xs hshape
    (conjunctionAccept _ _ xs
      (exactAccept _ xs (binaryValue data.member resultType (.projection 1) (numeral 1) typ parameter xs
        (andLeft hm) ht (projectionValue 1 xs)))
      (exactAccept _ xs (binaryValue data.member domain (.projection 1) (numeral 1) d parameter xs
        (andRight hm) hd (projectionValue 1 xs))))

theorem sourceCheckValue (data : Data) (raw parameter : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (SourceLambdaRootFactors data raw parameter))) :
    Nonempty (Derivation body Gamma (graph2 (sourceCheck data) (numeral 1) raw parameter)) := by
  apply sourceCases data raw parameter _ hf
  intro beta j Delta typ d e hj hf'
  simp only [graph2Rename,numeral,sucRelabel,zRelabel]
  exact sourceCheckAtFields data (raw.relabel j) (parameter.relabel j) typ d e hf'

theorem sourceCheckRecover (data : Data) (raw parameter : OTerm alpha)
    (hc : Nonempty (Derivation body Gamma (graph2 (sourceCheck data) (numeral 1) raw parameter))) :
    Nonempty (Derivation body Gamma (SourceLambdaRootFactors data raw parameter)) := by
  let xs : Fin 2 → OTerm alpha := ![raw,parameter]
  have hboth := conjunctionRecover _ _ xs hc
  have hs := shapeRecover raw parameter (andLeft hboth)
  apply shapeCases raw _ hs
  intro beta j Delta typ d e hj hf
  have hc' := renameInto hc j Delta hj
  simp only [graph2Rename,numeral,sucRelabel,zRelabel] at hc'
  simp only [sourceRename]
  let ys : Fin 2 → OTerm beta := ![raw.relabel j,parameter.relabel j]
  have hm := conjunctionRecover _ _ ys (andRight (conjunctionRecover _ _ ys hc'))
  have ht := resultTypeValue typ (raw.relabel j) (parameter.relabel j) (andLeft hf)
  have hd : Nonempty (Derivation body Delta (graph2 domain d (raw.relabel j) (parameter.relabel j))) :=
    unaryValue OriginalLambdaConstructor.domain (.projection 0) d (raw.relabel j) ys
      (andLeft (andRight hf)) (projectionValue 0 ys)
  have hmt := binaryRecover data.member resultType (.projection 1) (numeral 1) typ
    (parameter.relabel j) ys (exactRecover _ ys (andLeft hm)) ht (projectionValue 1 ys)
  have hmd := binaryRecover data.member domain (.projection 1) (numeral 1) d
    (parameter.relabel j) ys (exactRecover _ ys (andRight hm)) hd (projectionValue 1 ys)
  exact sourceIntro data (raw.relabel j) (parameter.relabel j) typ d e
    (andIntro (andLeft hf) (andIntro (andLeft (andRight hf))
      (andIntro (andLeft (andRight (andRight hf)))
        (andIntro (andRight (andRight (andRight hf))) (andIntro hmt hmd)))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalSourceCheckProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalSourceCheckProof
