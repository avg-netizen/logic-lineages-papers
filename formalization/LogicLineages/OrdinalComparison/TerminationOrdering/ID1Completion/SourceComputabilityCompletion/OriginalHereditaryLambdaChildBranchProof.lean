module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaChildRunProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaChildBranchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open OriginalHereditaryLambda OriginalHereditaryLambdaChildStateProof OriginalHereditaryLambdaChildControlProof
open OriginalHereditaryLambdaChildRunProof
open OriginalLambdaGuardLeafInternalProof (combine projectLeft projectRight)
open OriginalLambdaGuardLeafInternalChildProof (fourTuple)
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceConjunctionProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalRawListRepeat InternalRawListRepeatSyntaxProof InternalRawListRepeatProof
open InternalListCodecSupportProof (consGraph consGraphRename)
open InternalListCodecDecompositionSupportProof (reconstructNonzero)
open InternalApplicationStepPeelSupportProof (queryCases)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem tupleGraph (p : Program 4) (out : OTerm alpha) (xs : Fin 4 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (programGraph p out xs))) :
    Nonempty (Derivation body Delta (graph4 p out (xs 0) (xs 1) (xs 2) (xs 3))) := by
  change Nonempty (Derivation body Delta (programGraph p out
    (Fin.cons (xs 0) (Fin.cons (xs 1) (Fin.cons (xs 2) (Fin.cons (xs 3) Fin.elim0))))))
  rw [fourTuple]
  exact h

theorem fromTupleGraph (p : Program 4) (out : OTerm alpha) (xs : Fin 4 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph4 p out (xs 0) (xs 1) (xs 2) (xs 3)))) :
    Nonempty (Derivation body Delta (programGraph p out xs)) := by
  change Nonempty (Derivation body Delta (programGraph p out
    (Fin.cons (xs 0) (Fin.cons (xs 1) (Fin.cons (xs 2) (Fin.cons (xs 3) Fin.elim0)))))) at h
  rw [fourTuple] at h
  exact h

@[simp] theorem activeRename {beta : Type}
    (source target certificate parameter : OTerm alpha) (j : alpha → beta) :
    (LambdaNonbottom source target certificate parameter).relabel j =
      LambdaNonbottom (source.relabel j) (target.relabel j) (certificate.relabel j) (parameter.relabel j) := by
  change (graph4 OriginalLambdaGuardLeaf.sourceLambda (suc z) source target certificate parameter ⊓
    graph4 OriginalLambdaGuardLeaf.sameBottom z source target certificate parameter).relabel j = _
  simp only [conjunctionRename,graph4Rename,sucRelabel,zRelabel]
  rfl

def Recovered (oldStep : Program 4) (xs : Fin 4 → OTerm alpha) : Formula alpha :=
  programGraph OriginalLambdaGuardLeaf.matchingTarget (suc z) xs ⊓
    (programGraph lamPath (suc z) xs ⊓
      programGraph (OriginalLambdaGuardLeaf.childCheck (refined oldStep)) (suc z) xs)

@[simp] theorem recoveredRename {beta : Type} (oldStep : Program 4)
    (xs : Fin 4 → OTerm alpha) (j : alpha → beta) :
    (Recovered oldStep xs).relabel j = Recovered oldStep (fun i => (xs i).relabel j) := by
  simp only [Recovered,conjunctionRename,programRename,sucRelabel,zRelabel]

/-- One original front-cons commutation exposes the literal tail run. Failure
absorption rules out zero, so the actual active transition supplies every
parent guard and the SAME refined child composition. -/
theorem recoverAtCons (oldStep : Program 4) (xs : Fin 4 → OTerm alpha)
    (code head tail state out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph path code xs)))
    (hl : Nonempty (Derivation body Delta (programGraph live state xs)))
    (ha : Nonempty (Derivation body Delta (LambdaNonbottom (xs 0) (xs 1) (xs 2) (xs 3))))
    (hc : Nonempty (Derivation body Delta (consGraph code head tail)))
    (ht : Nonempty (Derivation body Delta (graph1 InternalListCodec.tailCode tail code)))
    (hr : Nonempty (Derivation body Delta (repeatGraph (transition oldStep) out code state)))
    (hf : Nonempty (Derivation body Delta (graph1 finish (suc z) out))) :
    Nonempty (Derivation body Delta (Recovered oldStep xs)) := by
  apply programCases (transition oldStep) (Fin.cons state Fin.elim0) _
  intro beta j Theta next hj hn
  rw [recoveredRename]
  have hp' := renameInto hp j Theta hj
  have hl' := renameInto hl j Theta hj
  have ha' := renameInto ha j Theta hj
  have hc' := renameInto hc j Theta hj
  have ht' := renameInto ht j Theta hj
  have hr' := renameInto hr j Theta hj
  have hf' := renameInto hf j Theta hj
  simp only [programRename] at hp' hl'
  rw [activeRename] at ha'
  rw [consGraphRename] at hc'
  rw [graph1Rename] at ht' hf'
  rw [repeatRename] at hr'
  simp only [sucRelabel,zRelabel] at hf'
  simp only [consTermRename,emptyRename] at hn
  let xx := fun i => (xs i).relabel j
  have htail := frontConsForward (transition oldStep) (code.relabel j) (head.relabel j)
    (tail.relabel j) (out.relabel j) (state.relabel j) next hc' hn hr'
  have hnz := acceptingRunNonzero oldStep (out.relabel j) (tail.relabel j) next htail hf'
  have hab := activeBranchRecover oldStep (state.relabel j) next hnz
    (transitionActiveRecover oldStep (state.relabel j) next (xx 0) (xx 1) (xx 2) (xx 3)
      (tupleGraph live (state.relabel j) xx hl') ha' hn)
  have hadvance := fromTupleGraph (advanceGuard oldStep) (suc z) xx
    (atLiveRecover (advanceGuard oldStep) (suc z) (state.relabel j)
      (xx 0) (xx 1) (xx 2) (xx 3) (tupleGraph live (state.relabel j) xx hl') (projectLeft hab))
  have hchildLive := fromTupleGraph childLive next xx
    (atLiveRecover childLive next (state.relabel j)
      (xx 0) (xx 1) (xx 2) (xx 3) (tupleGraph live (state.relabel j) xx hl') (projectRight hab))
  have hg := conjunctionRecover OriginalLambdaGuardLeaf.matchingTarget
    (InternalAcceptance.conjunction lamPath (OriginalLambdaGuardLeaf.childCheck oldStep)) xx hadvance
  have hi := conjunctionRecover lamPath (OriginalLambdaGuardLeaf.childCheck oldStep) xx (projectRight hg)
  exact combine (projectLeft hg) (combine (projectLeft hi)
    (hereditaryChildCheck oldStep xx (code.relabel j) (tail.relabel j) next (out.relabel j)
      hp' ht' (projectRight hi) hchildLive htail hf'))

theorem recoverAtRun (oldStep : Program 4) (xs : Fin 4 → OTerm alpha)
    (code state out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph path code xs)))
    (hl : Nonempty (Derivation body Delta (programGraph live state xs)))
    (ha : Nonempty (Derivation body Delta (LambdaNonbottom (xs 0) (xs 1) (xs 2) (xs 3))))
    (hr : Nonempty (Derivation body Delta (repeatGraph (transition oldStep) out code state)))
    (hf : Nonempty (Derivation body Delta (graph1 finish (suc z) out))) :
    Nonempty (Derivation body Delta (Recovered oldStep xs)) := by
  have hn := activeRunPathNonzero oldStep out code state (xs 0) (xs 1) (xs 2) (xs 3)
    (tupleGraph live state xs hl) ha hr hf
  apply queryCases (![InternalListCodec.headCode,InternalListCodec.tailCode] : Fin 2 → Program 1)
    (Fin.cons code Fin.elim0) _
  intro beta j ys Theta hj hq
  rw [recoveredRename]
  have hp' := renameInto hp j Theta hj
  have hl' := renameInto hl j Theta hj
  have ha' := renameInto ha j Theta hj
  have hr' := renameInto hr j Theta hj
  have hf' := renameInto hf j Theta hj
  have hn' := renameInto hn j Theta hj
  simp only [programRename] at hp' hl'
  rw [activeRename] at ha'
  rw [graph1Rename] at hf'
  rw [repeatRename] at hr'
  rw [notZeroRename] at hn'
  simp only [sucRelabel,zRelabel] at hf'
  have hhead := hq 0
  have htail := hq 1
  simp only [consTermRename,emptyRename] at hhead htail
  exact recoverAtCons oldStep (fun i => (xs i).relabel j)
    (code.relabel j) (ys 0) (ys 1) (state.relabel j) (out.relabel j) hp' hl' ha'
    (reconstructNonzero (code.relabel j) (ys 0) (ys 1) hn' hhead htail) htail hr' hf'

theorem recoverBranch (oldStep : Program 4) (xs : Fin 4 → OTerm alpha)
    (ha : Nonempty (Derivation body Delta (programGraph (refined oldStep) (suc z) xs)))
    (hn : Nonempty (Derivation body Delta (LambdaNonbottom (xs 0) (xs 1) (xs 2) (xs 3)))) :
    Nonempty (Derivation body Delta (Recovered oldStep xs)) := by
  have hg := projectRight (conjunctionRecover oldStep (guard oldStep) xs ha)
  apply queryCases (![path,live,run oldStep] : Fin 3 → Program 4) xs _
  intro beta j ys Theta hj hq
  rw [recoveredRename]
  have hg' := renameInto hg j Theta hj
  have hn' := renameInto hn j Theta hj
  simp only [programRename,sucRelabel,zRelabel,activeRename] at hg' hn'
  let xx := fun i => (xs i).relabel j
  have hf := unaryRecover finish (run oldStep) (suc z) (ys 2) xx hg' (hq 2)
  have hr := binaryRecover (repeatProgram (transition oldStep)) path live
    (ys 2) (ys 0) (ys 1) xx (hq 2) (hq 0) (hq 1)
  exact recoverAtRun oldStep xx (ys 0) (ys 1) (ys 2) (hq 0) (hq 1) hn' hr hf

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaChildBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaChildBranchProof
