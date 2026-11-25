module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicFrameZeroProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunLiftOwnProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRunTerminalFlagProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickOpenScratchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicTerminalRunProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue programRename outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseRawFunctionFrame (chosenFrame)
open NumberedWindowInternalSparseRawTick
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawTickOpenScratchProof (liveRead)
open NumberedWindowInternalSparseRawTickShapeEmitterProof (emitGraph)
open NumberedWindowInternalSparseRawRun (ownRun)
open NumberedWindowInternalSparseRawRunLiftOwnProof (initialTerm)
open NumberedWindowInternalLiteralRunTerminalFlagProof (exact_OpenTerminalFirstTickFlag)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalLiteralAtomicRawGuardOpenProof (D)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem liftLiveTerminal (p other : Program 3) (q w r flag : OTerm α)
    (live : D B Γ (programGraph (liveTick p other) (stateTerm flag z) ![q,w,r])) :
    D B Γ (programGraph (chosenTick p other) (stateTerm flag z) ![initialTerm (![q,w,r])]) := by
  let start := initialTerm (![q,w,r])
  let xs : Fin 1 → OTerm α := ![start]
  let stop := stateTerm flag z
  obtain ⟨found,hq,hw,hr⟩ := liveRead (body := B) (Γ := Γ) z q w r
  have call : D B Γ (programGraph (performLive p other) stop xs) := by
    apply compositionValue (liveTick p other) ![rowSource,rowWitness,rowDestination]
      stop xs ![q,w,r] live
    exact fun k => Fin.cases hq (Fin.cases hw (Fin.cases hr (fun e => Fin.elim0 e))) k
  exact successorBranchIntro stateFrame (.projection 0) (performLive p other) stop
    (packedBody [q,w,r]) xs found call

private theorem terminalZeroImpossible (p other : Program 3) (q w r : OTerm α) (goal : Formula α)
    (live : D B Γ (programGraph (liveTick p other) (stateTerm z z) ![q,w,r]))
    (success : D B Γ (programGraph (ownRun p other) (suc z) ![q,w,r])) : D B Γ goal := by
  obtain ⟨bad⟩ := exact_OpenTerminalFirstTickFlag p other q w r z
    (liftLiveTerminal p other q w r z live) success
  exact ⟨Derivation.explosion (sucNeZeroApply (symm bad))⟩

/-- If neither physical context callback can produce a child at the
initial tape, the original arbitrary own fuel cannot turn a later
scratch into a new successful root: only the original root callback
can pay the success. This is an actual object proof with the original
fuel, including zero, not a metatheoretic bound. -/
theorem exact_OpenLiteralTerminalOwnRunRoot (p other : Program 3) (q w r : OTerm α)
    (noFast : D B Γ (programGraph chosenFrame z ![q,w,r]))
    (noFallback : D B Γ (programGraph other z ![q,w,r]))
    (success : D B Γ (programGraph (ownRun p other) (suc z) ![q,w,r])) :
    D B Γ (programGraph (rootCall p) (suc z) ![q,w,r]) := by
  apply optionGraphCases tagFiveTest ![q,w,r] _
  · intro β j Δ keep no5
    rw [tripleInputsRename] at no5
    simp only [programRename,tripleInputsRename,sucRelabel,zRelabel]
    let a := q.relabel j
    let b := w.relabel j
    let c := r.relabel j
    let xs : Fin 3 → OTerm β := ![a,b,c]
    have strong := renameInto success j Δ keep
    simp only [programRename,tripleInputsRename,sucRelabel,zRelabel] at strong
    have reject := renameInto noFallback j Δ keep
    simp only [programRename,tripleInputsRename,zRelabel] at reject
    apply optionGraphCases rootTest xs (programGraph (rootCall p) (suc z) xs)
    · intro γ l Ω stay noRoot
      simp only [xs,tripleInputsRename] at noRoot
      simp only [xs,programRename,tripleInputsRename,sucRelabel,zRelabel]
      let ys : Fin 3 → OTerm γ := ![a.relabel l,b.relabel l,c.relabel l]
      have no := renameInto no5 l Ω stay
      have own := renameInto strong l Ω stay
      have fall := renameInto reject l Ω stay
      simp only [programRename,tripleInputsRename,sucRelabel,zRelabel] at no own fall
      have flush := emitGraph (constantZero 3) other z z ys (constantZeroValue ys) fall
      have inner := zeroBranchIntro rootTest (emitState (constantZero 3) other)
        (emitState (rootCall p) (constantZero 3)) (stateTerm z z) ys noRoot flush
      have live := zeroBranchIntro tagFiveTest
        (branch rootTest (emitState (constantZero 3) other) (emitState (rootCall p) (constantZero 3)))
        (emitState (constantZero 3) chosenFrame) (stateTerm z z) ys no inner
      exact terminalZeroImpossible p other (a.relabel l) (b.relabel l) (c.relabel l) _ live own
    · intro γ l Ω k stay atRoot
      simp only [xs,tripleInputsRename] at atRoot
      simp only [xs,programRename,tripleInputsRename,sucRelabel,zRelabel]
      let a' := a.relabel l
      let b' := b.relabel l
      let c' := c.relabel l
      apply programCases (rootCall p) ![a',b',c'] _
      intro δ m Ξ flag again actual
      rw [tripleInputsRename] at actual
      simp only [programRename,tripleInputsRename,sucRelabel,zRelabel]
      let ys : Fin 3 → OTerm δ := ![a'.relabel m,b'.relabel m,c'.relabel m]
      have rootYes := renameInto atRoot m Ξ again
      simp only [programRename,tripleInputsRename,sucRelabel] at rootYes
      have no := renameInto no5 l Ω stay
      simp only [programRename,tripleInputsRename,zRelabel] at no
      have no' := renameInto no m Ξ again
      simp only [programRename,tripleInputsRename,zRelabel] at no'
      have own := renameInto strong l Ω stay
      simp only [programRename,tripleInputsRename,sucRelabel,zRelabel] at own
      have own' := renameInto own m Ξ again
      simp only [programRename,tripleInputsRename,sucRelabel,zRelabel] at own'
      have stop := emitGraph (rootCall p) (constantZero 3) flag z ys actual (constantZeroValue ys)
      have inner := successorBranchIntro rootTest (emitState (constantZero 3) other)
        (emitState (rootCall p) (constantZero 3)) (stateTerm flag z) (k.relabel m) ys rootYes stop
      have live := zeroBranchIntro tagFiveTest
        (branch rootTest (emitState (constantZero 3) other) (emitState (rootCall p) (constantZero 3)))
        (emitState (constantZero 3) chosenFrame) (stateTerm flag z) ys no' inner
      have eq := exact_OpenTerminalFirstTickFlag p other (a'.relabel m) (b'.relabel m) (c'.relabel m) flag
        (liftLiveTerminal p other _ _ _ flag live) own'
      exact outputTransport (rootCall p) flag (suc z) ys eq actual
  · intro β j Δ k keep atFive
    rw [tripleInputsRename] at atFive
    simp only [programRename,tripleInputsRename,sucRelabel,zRelabel]
    let a := q.relabel j
    let b := w.relabel j
    let c := r.relabel j
    let xs : Fin 3 → OTerm β := ![a,b,c]
    have stop := renameInto noFast j Δ keep
    have own := renameInto success j Δ keep
    simp only [programRename,tripleInputsRename,sucRelabel,zRelabel] at stop own
    have base := emitGraph (constantZero 3) chosenFrame z z xs (constantZeroValue xs) stop
    have live := successorBranchIntro tagFiveTest
      (branch rootTest (emitState (constantZero 3) other) (emitState (rootCall p) (constantZero 3)))
      (emitState (constantZero 3) chosenFrame) (stateTerm z z) k xs atFive base
    exact terminalZeroImpossible p other a b c _ live own

#print axioms exact_OpenLiteralTerminalOwnRunRoot
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicTerminalRunProof
