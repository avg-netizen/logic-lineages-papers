module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepSpineProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaChildControlProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRepeatSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatchSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepHereditaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalAcceptanceSupportProof
open InternalControlGraphSupportProof InternalAcceptanceConjunctionProof InternalAcceptanceNormalizationProof
open InternalApplicationStepPeelSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalHereditaryLambda OriginalHereditaryLambdaChildStateProof
open OriginalHereditaryLambdaChildControlProof (liveNonzero nonzeroBranchIntro)
open OriginalTransparentVariableStepGuardProof (equalBranches)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Project the actual empty original position list from the concrete
certificate constructor, without assuming a path-selector result. -/
theorem certificatePath (s cert : OTerm alpha)
    (hc : Nonempty (Derivation body Delta
      (graph1 OriginalTransparentVariableStep.certificateCode cert s))) :
    Nonempty (Derivation body Delta (graph1 InternalUnpair.left z cert)) := by
  let suffix : Program 1 := pairOf
    (.composition BottomRepresentative.bottomCode (fun _ : Fin 1 => InternalUnpair.left))
    (pairOf (InternalFixedWindowVertexDispatch.constant 1 3)
      (InternalFixedWindowVertexDispatch.constant 1 0))
  apply programCases suffix (Fin.cons s Fin.elim0) _
  intro beta j Gamma payload hj hp
  simp only [graph1Rename,zRelabel]
  simp only [consTermRename,emptyRename] at hp
  have hc' := renameInto hc j Gamma hj
  simp only [graph1Rename] at hc'
  rw [OriginalTransparentVariableStep.certificateCode] at hc'
  let xs : Fin 1 → OTerm beta := Fin.cons (s.relabel j) Fin.elim0
  have hzero : Nonempty (Derivation body Gamma
      (programGraph (InternalFixedWindowVertexDispatch.constant 1 0) (z : OTerm beta) xs)) := by
    simpa only [SourceComputabilityFormulaSupportProof.numeral] using
      (InternalFixedWindowVertexDispatchSupportProof.constantValue (body := body) (Gamma := Gamma) 1 0 xs)
  have hpair := binaryRecover InternalPairing.pairing
    (InternalFixedWindowVertexDispatch.constant 1 0) suffix
    (cert.relabel j) z payload xs hc'
    hzero hp
  exact pairLeft (cert.relabel j) z payload hpair

/-- Same-type bottom pays the actual stop program on either lambda branch. -/
theorem stopBottom (s t cert parameter typ : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ s)))
    (hb : Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomCode t typ))) :
    Nonempty (Derivation body Delta (graph4 stop (suc z) s t cert parameter)) := by
  let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
  have htype := unaryValue InternalUnpair.left (.projection 0) typ s xs ht (projectionValue 0 xs)
  have hbottom := unaryValue BottomRepresentative.bottomCode (leftOf (.projection 0)) t typ xs hb htype
  have hsame := sameAccept (.projection 1) OriginalConstructorLeaf.expectedBottom t xs
    (projectionValue 1 xs) hbottom
  exact equalBranches _ _ _ (suc z) xs
    (InternalLessThanSupportProof.oneConstantValue xs)
    (normalizeAccept OriginalLambdaGuardLeaf.sameBottom xs hsame)

theorem guardAtLive (oldStep : Program 4) (s t cert parameter typ state : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ s)))
    (hb : Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomCode t typ)))
    (hc : Nonempty (Derivation body Delta
      (graph1 OriginalTransparentVariableStep.certificateCode cert s)))
    (hl : Nonempty (Derivation body Delta (graph4 live state s t cert parameter))) :
    Nonempty (Derivation body Delta (graph4 (guard oldStep) (suc z) s t cert parameter)) := by
  let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
  have hp := unaryValue InternalUnpair.left (.projection 2) z cert xs
    (certificatePath s cert hc) (projectionValue 2 xs)
  have hr := binaryValue (InternalRawListRepeat.repeatProgram (transition oldStep)) path live
    state z state xs (InternalRawListRepeatSupportProof.repeatZeroValue (transition oldStep) state) hp hl
  have hs := atLiveValue stop (suc z) state s t cert parameter hl (stopBottom s t cert parameter typ ht hb)
  have hf := nonzeroBranchIntro (.projection (0 : Fin 1)) (InternalAcceptance.constantZero 1)
    (atState stop) (suc z) state (Fin.cons state Fin.elim0)
    (projectionValue 0 (Fin.cons state Fin.elim0)) (liveNonzero state s t cert parameter hl) hs
  exact unaryValue finish (run oldStep) (suc z) state xs hf hr

/-- Original nil-path recurrence leaves the SAME actual live state; no
child acceptance, native calibration or internal transition law is assumed. -/
theorem nilGuard (oldStep : Program 4) (s t cert parameter typ : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ s)))
    (hb : Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomCode t typ)))
    (hc : Nonempty (Derivation body Delta
      (graph1 OriginalTransparentVariableStep.certificateCode cert s))) :
    Nonempty (Derivation body Delta (graph4 (guard oldStep) (suc z) s t cert parameter)) := by
  let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
  apply programCases live xs _
  intro beta j Gamma state hj hl
  simp only [graph4Rename,sucRelabel,zRelabel]
  simp only [xs,consTermRename,emptyRename] at hl
  have ht' := renameInto ht j Gamma hj
  have hb' := renameInto hb j Gamma hj
  have hc' := renameInto hc j Gamma hj
  simp only [graph1Rename] at ht' hb' hc'
  exact guardAtLive oldStep (s.relabel j) (t.relabel j) (cert.relabel j)
    (parameter.relabel j) (typ.relabel j) state ht' hb' hc' hl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepHereditaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepHereditaryProof
