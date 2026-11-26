module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalLiteralSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalShapeAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphReconstructionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalLiteralProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalTransparentLambdaValidity OriginalTransparentLambdaValidityInternal
open OriginalTransparentLambdaValidityInternalShapeSyntaxProof OriginalTransparentLambdaValidityInternalLiteralSyntaxProof
open OriginalTransparentLambdaValidityInternalShapeAcceptanceProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem literalAtShapeFields (raw typ d e : OTerm alpha)
    (ht : Nonempty (Derivation body Gamma (TagIs 1 raw)))
    (hf : Nonempty (Derivation body Gamma (shapeFields raw typ d e))) :
    Nonempty (Derivation body Gamma (LiteralLambda raw)) := by
  apply programCases OriginalLambdaConstructor.bodyCode (Fin.cons e (Fin.cons raw Fin.elim0)) _
  intro beta j Delta b hj hb
  have ht' := renameInto ht j Delta hj
  have hf' := renameInto hf j Delta hj
  simp only [TagIs,graph1Rename,numeral,sucRelabel,zRelabel] at ht'
  simp only [shapeFields,conjunctionRename,graph1Rename,graph2Rename] at hf'
  simp only [consTermRename,emptyRename] at hb
  simp only [literalRename]
  have fields : Nonempty (Derivation body Delta
      (OriginalLambdaConstructor.Fields (raw.relabel j) (d.relabel j) (e.relabel j) b (typ.relabel j))) :=
    andIntro ht' (andIntro (andLeft hf')
      (andIntro (andRight (andRight (andRight hf'))) (andIntro (andLeft (andRight hf')) hb)))
  exact literalIntro (raw.relabel j) (d.relabel j) (e.relabel j) b (typ.relabel j)
    (andIntro fields (OriginalLambdaConstructorGraphReconstructionProof.constructorReconstruction
      (raw.relabel j) (d.relabel j) (e.relabel j) b (typ.relabel j) fields))

theorem literalValue (raw parameter : OTerm alpha)
    (ht : Nonempty (Derivation body Gamma (TagIs 1 raw)))
    (hs : Nonempty (Derivation body Gamma (graph2 lambdaShape (numeral 1) raw parameter))) :
    Nonempty (Derivation body Gamma (LiteralLambda raw)) := by
  apply shapeCases raw _ (shapeRecover raw parameter hs)
  intro beta j Delta typ d e hj hf
  have ht' := renameInto ht j Delta hj
  simp only [TagIs,graph1Rename,numeral,sucRelabel,zRelabel] at ht'
  simp only [literalRename]
  exact literalAtShapeFields (raw.relabel j) typ d e ht' hf

theorem literalRecover (raw parameter : OTerm alpha)
    (hl : Nonempty (Derivation body Gamma (LiteralLambda raw))) :
    Nonempty (Derivation body Gamma
      (TagIs 1 raw ⊓ graph2 lambdaShape (numeral 1) raw parameter)) := by
  apply literalCases raw _ hl
  intro beta j Delta d e b typ hj hf
  simp only [conjunctionRename,TagIs,graph1Rename,graph2Rename,numeral,sucRelabel,zRelabel]
  have fields := andLeft hf
  have ha := andLeft (andRight (andRight fields))
  have htail := andLeft (andRight (InternalListCodecSupportProof.consDestruction typ d e ha))
  have hshape := shapeAtFields (raw.relabel j) (parameter.relabel j) typ d e
    (andIntro (andLeft (andRight fields))
      (andIntro (andLeft (andRight (andRight (andRight fields)))) (andIntro htail ha)))
  exact andIntro (andLeft fields) hshape

theorem actualOriginalTransparentInternalLiteralLambda :
    OriginalTransparentLambdaValidityInternalTargets.ActualOriginalTransparentInternalLiteralLambda := by
  intro body alpha raw parameter
  let A := TagIs 1 raw ⊓ graph2 lambdaShape (numeral 1) raw parameter
  let B := LiteralLambda raw
  have ha : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hf⟩ := literalValue raw parameter (andLeft ha) (andRight ha)
  obtain ⟨hb⟩ := literalRecover (body := body) (Gamma := [B]) raw parameter
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalLiteralProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalLiteralProof
