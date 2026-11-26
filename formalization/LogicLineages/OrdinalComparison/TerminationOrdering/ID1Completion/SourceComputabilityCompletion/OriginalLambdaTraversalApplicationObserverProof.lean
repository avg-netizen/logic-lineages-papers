module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalApplicationObserverNeutralProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalObserverDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSpineApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarBottomTestZeroProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalApplicationObserverProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationStepPeelSupportProof
open InternalTagArithmeticSyntaxProof (z)
open InternalTagArithmeticSupportProof (refl)
open OriginalConstructorShapeApplicationProof
open OriginalLambdaTraversalObserver
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The original application constructors preserve all five observers when
the function's actual root mark and bottom-spine measure are shared. The
spine equation follows the FUNCTION child, and all actual child types remain. -/
theorem atConstructors (arrow d e fn arg fnOut argOut input out functionMark spineMark mark : OTerm alpha)
    (har : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode arrow d e)))
    (hft : Nonempty (Derivation body Delta (graph1 InternalUnpair.left arrow fn)))
    (hat : Nonempty (Derivation body Delta (graph1 InternalUnpair.left d arg)))
    (hfot : Nonempty (Derivation body Delta (graph1 InternalUnpair.left arrow fnOut)))
    (haot : Nonempty (Derivation body Delta (graph1 InternalUnpair.left d argOut)))
    (hi : Nonempty (Derivation body Delta (graph4 application input d e fn arg)))
    (ho : Nonempty (Derivation body Delta (graph4 application out d e fnOut argOut)))
    (hfm : Nonempty (Derivation body Delta (graph1 OriginalConstructorShape.mark functionMark fn)))
    (hfom : Nonempty (Derivation body Delta (graph1 OriginalConstructorShape.mark functionMark fnOut)))
    (hsm : Nonempty (Derivation body Delta (graph1 BottomSpineMeasure.measure spineMark fn)))
    (hfsm : Nonempty (Derivation body Delta (graph1 BottomSpineMeasure.measure spineMark fnOut))) :
    Nonempty (Derivation body Delta (observations out input mark)) := by
  have root := iffCompose (OriginalConstructorShape.markGraph mark out)
    (graph2 InternalPairing.pairing mark positionTerm d) (OriginalConstructorShape.markGraph mark input)
    (applicationMarkIff mark d out (rawFields d e fnOut argOut out ho))
    (iffFlip _ _ (applicationMarkIff mark d input (rawFields d e fn arg input hi)))
  have hvariable := BottomRepresentativeInternalProof.indicatorIff OriginalVariableRepresentative.variableMark
    mark out input z z
    (OriginalVariableRepresentativeApplicationMarkProof.applicationMarkZero d e fnOut argOut out ho)
    (OriginalVariableRepresentativeApplicationMarkProof.applicationMarkZero d e fn arg input hi) ⟨refl z⟩
  have neutral := OriginalLambdaTraversalApplicationObserverNeutralProof.atRootMark
    d e fn arg fnOut argOut input out functionMark mark hi ho hfm hfom
  have spine := OriginalApplicationSidecarSpineApplicationProof.atFunctionMark
    arrow d e fn arg fnOut argOut input out spineMark mark har hft hat hfot haot hi ho hsm hfsm
  have bottom := BottomRepresentativeInternalProof.indicatorIff BottomRepresentative.bottomTest
    mark out input z z
    (OriginalApplicationSidecarBottomTestZeroProof.zeroOfNonacceptance out
      (BottomApplicationProof.rawNotBottom d e fnOut argOut out ho))
    (OriginalApplicationSidecarBottomTestZeroProof.zeroOfNonacceptance input
      (BottomApplicationProof.rawNotBottom d e fn arg input hi)) ⟨refl z⟩
  exact andIntro root (andIntro hvariable (andIntro neutral (andIntro spine bottom)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalApplicationObserverProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalApplicationObserverProof
