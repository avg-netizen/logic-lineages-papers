module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaChildStateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRepeatProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepRunProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalAcceptanceNormalizationProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalTransparentLambdaStep
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- At an actual successful hop, the independent transition advances to the
actual child live state. No oldStep is invoked by this graph construction. -/
theorem transitionAtLive (source : Program 2)
    (s t cert parameter state next : OTerm alpha)
    (hl : Nonempty (Derivation body Delta
      (graph4 OriginalHereditaryLambda.live state s t cert parameter)))
    (hg : Nonempty (Derivation body Delta (graph4 (hopGuard source) (suc z) s t cert parameter)))
    (hc : Nonempty (Derivation body Delta
      (graph4 OriginalHereditaryLambda.childLive next s t cert parameter))) :
    Nonempty (Derivation body Delta (graph1 (transition source) next state)) := by
  have hguard := OriginalHereditaryLambdaChildStateProof.atLiveValue
    (hopGuard source) (suc z) state s t cert parameter hl hg
  have hchild := OriginalHereditaryLambdaChildStateProof.atLiveValue
    OriginalHereditaryLambda.childLive next state s t cert parameter hl hc
  exact successorBranchIntro _ _ _ next z (Fin.cons state Fin.elim0)
    (normalizeAccept _ (Fin.cons state Fin.elim0) hguard) hchild

/-- Actual front-cons recurrence, forward, at unchanged code values. -/
theorem runForward (source : Program 2)
    (xs ys : Fin 4 → OTerm alpha) (code tail state next out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.path code xs)))
    (ht : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.path tail ys)))
    (hl : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.live state xs)))
    (hn : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.live next ys)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code z tail)))
    (hstep : Nonempty (Derivation body Delta (graph1 (transition source) next state)))
    (hr : Nonempty (Derivation body Delta (programGraph (run source) out xs))) :
    Nonempty (Derivation body Delta (programGraph (run source) out ys)) := by
  have hrepeat := binaryRecover (InternalRawListRepeat.repeatProgram (transition source))
    OriginalHereditaryLambda.path OriginalHereditaryLambda.live out code state xs hr hp hl
  have htail := InternalRawListRepeatProof.frontConsForward (transition source)
    code z tail out state next hc hstep hrepeat
  exact binaryValue (InternalRawListRepeat.repeatProgram (transition source))
    OriginalHereditaryLambda.path OriginalHereditaryLambda.live out tail next ys htail ht hn

/-- The converse recurrence proves equality of the SAME normalizer, not
acceptance merely of the unrefined oldStep at a child. -/
theorem runBackward (source : Program 2)
    (xs ys : Fin 4 → OTerm alpha) (code tail state next out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.path code xs)))
    (ht : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.path tail ys)))
    (hl : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.live state xs)))
    (hn : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.live next ys)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code z tail)))
    (hstep : Nonempty (Derivation body Delta (graph1 (transition source) next state)))
    (hr : Nonempty (Derivation body Delta (programGraph (run source) out ys))) :
    Nonempty (Derivation body Delta (programGraph (run source) out xs)) := by
  have hrepeat := binaryRecover (InternalRawListRepeat.repeatProgram (transition source))
    OriginalHereditaryLambda.path OriginalHereditaryLambda.live out tail next ys hr ht hn
  have hparent := InternalRawListRepeatProof.frontConsBackward (transition source)
    code z tail out state next hc hstep hrepeat
  exact binaryValue (InternalRawListRepeat.repeatProgram (transition source))
    OriginalHereditaryLambda.path OriginalHereditaryLambda.live out code state xs hparent hp hl

/-- Transport an arbitrary original leaf output along the exact common
normalized state, without asking oldStep for any additional acceptance. -/
theorem refinedForward (source : Program 2) (oldStep : Program 4)
    (xs ys : Fin 4 → OTerm alpha) (code tail state next out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.path code xs)))
    (ht : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.path tail ys)))
    (hl : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.live state xs)))
    (hn : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.live next ys)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code z tail)))
    (hstep : Nonempty (Derivation body Delta (graph1 (transition source) next state)))
    (hout : Nonempty (Derivation body Delta (programGraph (refined source oldStep) out xs))) :
    Nonempty (Derivation body Delta (programGraph (refined source oldStep) out ys)) := by
  apply programCases (run source) xs _
  intro beta j Gamma result hj hr
  simp only [programRename]
  have hp' := renameInto hp j Gamma hj
  have ht' := renameInto ht j Gamma hj
  have hl' := renameInto hl j Gamma hj
  have hn' := renameInto hn j Gamma hj
  have hc' := renameInto hc j Gamma hj
  have hstep' := renameInto hstep j Gamma hj
  have hout' := renameInto hout j Gamma hj
  simp only [programRename] at hp' ht' hl' hn' hout'
  simp only [graph2Rename,zRelabel] at hc'
  simp only [graph1Rename] at hstep'
  have hterminal := unaryRecover (OriginalHereditaryLambda.atState oldStep) (run source)
    (out.relabel j) result (fun i => (xs i).relabel j) hout' hr
  have hr' := runForward source (fun i => (xs i).relabel j) (fun i => (ys i).relabel j)
    (code.relabel j) (tail.relabel j) (state.relabel j) (next.relabel j) result
    hp' ht' hl' hn' hc' hstep' hr
  exact unaryValue (OriginalHereditaryLambda.atState oldStep) (run source)
    (out.relabel j) result (fun i => (ys i).relabel j) hterminal hr'

/-- Transport an arbitrary original leaf output along the exact common
normalized state, without asking oldStep for any additional acceptance. -/
theorem refinedBackward (source : Program 2) (oldStep : Program 4)
    (xs ys : Fin 4 → OTerm alpha) (code tail state next out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.path code xs)))
    (ht : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.path tail ys)))
    (hl : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.live state xs)))
    (hn : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.live next ys)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code z tail)))
    (hstep : Nonempty (Derivation body Delta (graph1 (transition source) next state)))
    (hout : Nonempty (Derivation body Delta (programGraph (refined source oldStep) out ys))) :
    Nonempty (Derivation body Delta (programGraph (refined source oldStep) out xs)) := by
  apply programCases (run source) ys _
  intro beta j Gamma result hj hr
  simp only [programRename]
  have hp' := renameInto hp j Gamma hj
  have ht' := renameInto ht j Gamma hj
  have hl' := renameInto hl j Gamma hj
  have hn' := renameInto hn j Gamma hj
  have hc' := renameInto hc j Gamma hj
  have hstep' := renameInto hstep j Gamma hj
  have hout' := renameInto hout j Gamma hj
  simp only [programRename] at hp' ht' hl' hn' hout'
  simp only [graph2Rename,zRelabel] at hc'
  simp only [graph1Rename] at hstep'
  have hterminal := unaryRecover (OriginalHereditaryLambda.atState oldStep) (run source)
    (out.relabel j) result (fun i => (ys i).relabel j) hout' hr
  have hr' := runBackward source (fun i => (xs i).relabel j) (fun i => (ys i).relabel j)
    (code.relabel j) (tail.relabel j) (state.relabel j) (next.relabel j) result
    hp' ht' hl' hn' hc' hstep' hr
  exact unaryValue (OriginalHereditaryLambda.atState oldStep) (run source)
    (out.relabel j) result (fun i => (xs i).relabel j) hterminal hr'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepRunProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepRunProof
