module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunRootTapeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunLiftOwnProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunTerminalChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickOpenScratchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunRootProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof
  (programRename compositionValue outputTransport valueUnique)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody rawConsRename)
open NumberedWindowInternalSparseRawFunctionFrame (chosenFrame)
open NumberedWindowInternalSparseRawFunctionFrameTargets (frameValueTerm)
open NumberedWindowInternalSparseRawTick
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawTickOpenScratchProof (liveRead)
open NumberedWindowInternalSparseRawTickShapeEmitterProof (emitGraph)
open NumberedWindowInternalSparseRawRun (ownState ownRun)
open NumberedWindowInternalSparseRawRunTerminalChecks (exact_OpenRawTerminalLoop)
open NumberedWindowInternalSparseRawRunSuccessProof (headRead terminalOwnRun)
open NumberedWindowInternalSparseRawRunShiftProof (shiftLate)
open NumberedWindowInternalSparseRawRunLiftOwnProof (initialTerm loopOwn)
open NumberedWindowInternalSparseRawRunRootTargets (rootWitnessTerm)
open NumberedWindowInternalSparseRawRunRootTapeProof
  (rootTape tagFiveZero rootReports rootCallAccept rootCallRecover)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem witnessRename {β : Type} (payload : OTerm α) (j : α → β) :
    (rootWitnessTerm payload).relabel j = rootWitnessTerm (payload.relabel j) := by
  unfold rootWitnessTerm
  rw [rawConsRename,rawConsRename,zRelabel]

theorem tapeRename {β : Type} (q payload r : OTerm α) (j : α → β) :
    (fun i => (rootTape q payload r i).relabel j) =
      rootTape (q.relabel j) (payload.relabel j) (r.relabel j) := by
  funext i
  exact Fin.cases rfl (Fin.cases (witnessRename payload j) (Fin.cases rfl
    (fun a => Fin.elim0 a))) i

theorem tripleRename {β : Type} (q payload r : OTerm α) (j : α → β) :
    (fun i : Fin 3 => (![q,payload,r] i).relabel j) =
      ![q.relabel j,payload.relabel j,r.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun a => Fin.elim0 a))) i

/-- Actual live dispatcher on the literal root tape: tag5 test zero, root
test one, so the root emitter is selected with the supplied root output. -/
theorem liveRoot (p other : Program 3) (q payload r c : OTerm α)
    (hc : Nonempty (Derivation body Γ (programGraph (rootCall p) c (rootTape q payload r)))) :
    Nonempty (Derivation body Γ
      (programGraph (liveTick p other) (stateTerm c z) (rootTape q payload r))) := by
  let xs := rootTape q payload r
  let fallback : Program 3 := emitState (constantZero 3) other
  let rooted : Program 3 := emitState (rootCall p) (constantZero 3)
  have emitted : Nonempty (Derivation body Γ (programGraph rooted (stateTerm c z) xs)) :=
    emitGraph (rootCall p) (constantZero 3) c z xs hc (constantZeroValue xs)
  have inner := successorBranchIntro rootTest fallback rooted (stateTerm c z) z xs
    (rootReports q payload r).1 emitted
  exact zeroBranchIntro tagFiveTest (branch rootTest fallback rooted)
    (emitState (constantZero 3) chosenFrame) (stateTerm c z) xs (tagFiveZero q payload r) inner

theorem tickRoot (p other : Program 3) (flag q payload r c : OTerm α)
    (hc : Nonempty (Derivation body Γ (programGraph (rootCall p) c (rootTape q payload r)))) :
    Nonempty (Derivation body Γ (programGraph (chosenTick p other) (stateTerm c z)
      ![stateTerm flag (frameValueTerm q (rootWitnessTerm payload) r)])) := by
  let w := rootWitnessTerm payload
  let initial := stateTerm flag (frameValueTerm q w r)
  let xs : Fin 1 → OTerm α := ![initial]
  obtain ⟨found,hq,hw,hr⟩ := liveRead (body := body) (Γ := Γ) flag q w r
  have live := liveRoot p other q payload r c hc
  have h : Nonempty (Derivation body Γ (unary (performLive p other) (stateTerm c z) initial)) := by
    unfold unary performLive
    apply compositionValue (liveTick p other) ![rowSource,rowWitness,rowDestination]
      (stateTerm c z) xs ![q,w,r] live
    intro i
    exact Fin.cases hq (Fin.cases hw (Fin.cases hr (fun e => Fin.elim0 e))) i
  exact successorBranchIntro stateFrame (.projection 0) (performLive p other) (stateTerm c z)
    (packedBody [q,w,r]) xs found h

/-- The whole actual own state on a literal root tape: one root tick,
then the #697 terminal loop on the remaining witness fuel. The witness
code is literally a successor, so no order premise is needed. -/
theorem rootOwnState (p other : Program 3) (q payload r c : OTerm α)
    (hc : Nonempty (Derivation body Γ (programGraph (rootCall p) c (rootTape q payload r)))) :
    Nonempty (Derivation body Γ
      (programGraph (ownState p other) (stateTerm c z) (rootTape q payload r))) := by
  let xs := rootTape q payload r
  let terminal := stateTerm c z
  let m : OTerm α := pairTerm z (rawCons payload z)
  have tick := tickRoot p other z q payload r c hc
  obtain ⟨loop⟩ := exact_OpenRawTerminalLoop body p other α c m
  have late := shiftLate p other (initialTerm xs) terminal m terminal tick
    ⟨weakenClosed loop Γ⟩
  exact loopOwn p other terminal xs late

theorem rootRunAccept (p other : Program 3) (q payload r : OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph p (suc z) ![q,payload,r]))) :
    Nonempty (Derivation body Γ
      (programGraph (ownRun p other) (suc z) (rootTape q payload r))) :=
  terminalOwnRun p other z (rootTape q payload r)
    (rootOwnState p other q payload r (suc z) (rootCallAccept p q payload r h))

/-- Converse: original totality supplies the root call's output, the
forward construction and functionality of the own run identify it with
the supplied one, and the actual normalizer is inverted at one. -/
theorem rootRunRecover (p other : Program 3) (q payload r : OTerm α)
    (h : Nonempty (Derivation body Γ
      (programGraph (ownRun p other) (suc z) (rootTape q payload r)))) :
    Nonempty (Derivation body Γ (programGraph p (suc z) ![q,payload,r])) := by
  apply programCases (rootCall p) (rootTape q payload r) _
  intro β j Δ c hj hc
  rw [programRename,sucRelabel,zRelabel,tripleRename]
  rw [tapeRename] at hc
  have h' := renameInto h j Δ hj
  rw [programRename,sucRelabel,zRelabel,tapeRename] at h'
  let xs := rootTape (q.relabel j) (payload.relabel j) (r.relabel j)
  have state := rootOwnState p other (q.relabel j) (payload.relabel j) (r.relabel j) c hc
  have read : Nonempty (Derivation body Δ (programGraph (ownRun p other) c xs)) := by
    apply compositionValue cellHead (fun _ : Fin 1 => ownState p other) c xs ![stateTerm c z]
      (headRead c z)
    intro i
    obtain rfl := Fin.eq_zero i
    exact state
  have e := valueUnique (ownRun p other) c (suc z) xs read h'
  exact rootCallRecover p (q.relabel j) (payload.relabel j) (r.relabel j)
    (outputTransport (rootCall p) c (suc z) xs e hc)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunRootProof
