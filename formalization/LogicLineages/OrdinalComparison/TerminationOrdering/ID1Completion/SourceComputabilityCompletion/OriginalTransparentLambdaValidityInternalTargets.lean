module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open InternalOriginalUniformDescentSelection (Data)
open OriginalTransparentLambdaValidity OriginalTransparentLambdaValidityInternal

/-- Exact internal selector equations on every raw input. The runtime
parameter is ignored ONLY by these literal selector ASTs. No native result,
calibration, decoded type or Gamma, or source validity is assumed. -/
def ActualOriginalTransparentInternalSelectors : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type)
    (out raw parameter : OTerm alpha),
  Nonempty (Derivation body []
    ((graph2 resultType out raw parameter).iff (graph1 InternalUnpair.left out raw))) ∧
  Nonempty (Derivation body []
    ((graph2 tag out raw parameter).iff (graph1 OriginalLambdaConstructor.tag out raw))) ∧
  Nonempty (Derivation body []
    ((graph2 domain out raw parameter).iff (graph1 OriginalLambdaConstructor.domain out raw))) ∧
  Nonempty (Derivation body []
    ((graph2 codomain out raw parameter).iff (CodomainGraph out raw)))

/-- Full-output arithmetic graph factorization of the ACTUAL shape AST.
Type zero and mismatched payload domain reject. A literal lambda tag is
neither assumed nor enough to make the shape formula hold. -/
def ActualOriginalTransparentInternalShape : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type)
    (out raw parameter : OTerm alpha),
  Nonempty (Derivation body []
    ((graph2 lambdaShape out raw parameter).iff
      (BooleanOutput out (LambdaShape raw))))

/-- Full-output sourceRoot equation for ARBITRARY Data, including opaque
non-Boolean outputs. Source lambda acceptance needs shape and BOTH original
outer/domain memberships, not a supplied source/body validity hypothesis. -/
def ActualOriginalTransparentInternalSourceRoot : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (alpha : Type)
    (out raw parameter : OTerm alpha),
  Nonempty (Derivation body []
    ((graph2 (sourceRoot data) out raw parameter).iff
      (SourceRootOutput data out raw parameter)))

/-- Full-output targetRoot equation for ARBITRARY Data. Tag two is one,
tag one checks only shape, and every other tag calls the exact oldTarget
leaf. In particular no source-window membership is added to the target. -/
def ActualOriginalTransparentInternalTargetRoot : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (alpha : Type)
    (out raw parameter : OTerm alpha),
  Nonempty (Derivation body []
    ((graph2 (targetRoot data) out raw parameter).iff
      (TargetRootOutput data out raw parameter)))

/-- Shape plus the actual lambda tag is equivalent to the internally opened
ORIGINAL constructor and its exact fields. The same raw value is rebuilt;
the repacked body, domain, codomain and outer arrow are internal witnesses.
No typed body, accepted body or native constructor calibration is assumed. -/
def ActualOriginalTransparentInternalLiteralLambda : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (raw parameter : OTerm alpha),
  Nonempty (Derivation body []
    ((TagIs 1 raw ⊓ graph2 lambdaShape (numeral 1) raw parameter).iff
      (LiteralLambda raw)))

/-- At EXACT original bottom codes, both LOCAL validators ignore only the
encoded Gamma component. The SAME outer raw context is retained, including
malformed contexts. N = normalizedData rawData captures bottom-normalized
original source/target leaves. No assertion of Gamma-invariance for arbitrary
nonbottom terms, calibration, Boolean leaves or successful run is supplied.
This is an internal full-output equation for the original framed machine. -/
def ActualOriginalTransparentInternalBottomParameter : Prop :=
  ∀ (body : Positive (Fin 1)) (rawData : Data) (alpha : Type)
    (out raw parameter context encodedGamma contextOnly : OTerm alpha),
  Nonempty (Derivation body []
    ((graph2 InternalPairing.pairing parameter context encodedGamma ⊓
      (graph2 InternalPairing.pairing contextOnly context OrdinaryArithmetic.zeroTerm ⊓
        BottomRepresentative.bottomGraph (numeral 1) raw)).imp
      (((graph2 (sourceValidator rawData) out raw parameter).iff
          (graph2 (sourceValidator rawData) out raw contextOnly)) ⊓
        ((graph2 (targetValidator rawData) out raw parameter).iff
          (graph2 (targetValidator rawData) out raw contextOnly)))))

/-- Applying the EXISTING bottom-parameter normalization to either LOCAL
transparent validator preserves its entire internal graph on every input.
Off exact bottom the AST takes the unchanged branch; at exact bottom the
previous internal parameter law pays the slice. This is not normalization
or lambda closure of the eventual final application-fold source Program. -/
def ActualOriginalTransparentInternalBottomNormalization : Prop :=
  ∀ (body : Positive (Fin 1)) (rawData : Data) (alpha : Type)
    (out raw parameter : OTerm alpha),
  Nonempty (Derivation body []
    ((graph2 (BottomParameter.normalized (sourceValidator rawData)) out raw parameter).iff
      (graph2 (sourceValidator rawData) out raw parameter))) ∧
  Nonempty (Derivation body []
    ((graph2 (BottomParameter.normalized (targetValidator rawData)) out raw parameter).iff
      (graph2 (targetValidator rawData) out raw parameter)))

/-- Exact full-output lambda recurrence of LOCAL HS, not of a final source
fold. Shape, both normalized original memberships, actual body acceptance
and its extended-Gamma parameter occur on the CONCLUSION side. The child
uses the IDENTICAL HS at its own payload+1 fuel. This follows only from an
independent internal recurrence and callback graph laws, never native HS
equality to rawData.oldSource. The raw Data tuple is wholly arbitrary. -/
def ActualOriginalTransparentInternalSourceLambda : Prop :=
  ∀ (body : Positive (Fin 1)) (rawData : Data) (alpha : Type)
    (out raw parameter : OTerm alpha),
  Nonempty (Derivation body []
    ((TagIs 1 raw).imp
      ((graph2 (sourceValidator rawData) out raw parameter).iff
        (BooleanOutput out (SourceLambdaFactors rawData raw parameter)))))

/-- Exact full-output lambda recurrence of LOCAL HT at the actual body and
extended encoded Gamma, with the SAME raw outer context. The target has no
membership filter and no source-acceptance premise. Neither child acceptance
nor body typing is assumed; both acceptance and rejection are characterized. -/
def ActualOriginalTransparentInternalTargetLambda : Prop :=
  ∀ (body : Positive (Fin 1)) (rawData : Data) (alpha : Type)
    (out raw parameter : OTerm alpha),
  Nonempty (Derivation body []
    ((TagIs 1 raw).imp
      ((graph2 (targetValidator rawData) out raw parameter).iff
        (BooleanOutput out (TargetLambdaFactors rawData raw parameter)))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalTargets
