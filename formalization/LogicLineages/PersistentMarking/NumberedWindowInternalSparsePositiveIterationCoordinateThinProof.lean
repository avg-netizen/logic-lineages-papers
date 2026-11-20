module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateThinLeavesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateThinProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalListCodec (consCode)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalSparsePositiveFold
open NumberedWindowInternalSparsePositiveFoldTargets (stepGraph)
open NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof (call6)
open NumberedWindowInternalSparsePositiveIterationTargets
open NumberedWindowInternalSparsePositiveIterationCoordinateThinGraphProof
open NumberedWindowInternalSparsePositiveIterationCoordinateThinLeavesProof

private theorem advanceStable (r : Program 5) (l : Program 3) : Stable (advanceAtCell r l) :=
  stableCompose (advance r l) ![.projection 2,.projection 3,scratchCurrent,onCursor cellHead]
    (fun i => Fin.cases context (Fin.cases ty (Fin.cases current
      (Fin.cases (readCell cellHead) (fun u => Fin.elim0 u)))) i)

private theorem updateStable (r : Program 5) (l : Program 3) : Stable (updateCell r l) :=
  binary consCode (onCursor cellTail) (advanceAtCell r l) (readCell cellTail) (advanceStable r l)

private theorem deadStable : Stable dead :=
  binary consCode (constantZero 6) (constantZero 6) zero zero

private theorem stepStable (r : Program 5) (l : Program 3) : Stable (iterateStep r l) :=
  choice scratchCursor (.projection 1) _ cursor prior
    (choice (onCursor cellGood) dead (updateCell r l) (readCell cellGood) deadStable (updateStable r l))

theorem moveUnused {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (raw : Program 5) (least : Program 3)
    (out prior c ty k start cert k' start' cert' : OTerm α)
    (h : Nonempty (Derivation body Γ (stepGraph raw least out k prior c ty start cert))) :
    Nonempty (Derivation body Γ (stepGraph raw least out k' prior c ty start' cert')) := by
  apply stepStable raw least body α Γ out
    (call6 k prior c ty start cert) (call6 k' prior c ty start' cert') _ h
  intro i hi
  rcases hi with rfl | rfl | rfl <;> rfl

theorem coordinates : OpenStepCoordinates := by
  intro body raw least α out prior c ty k start cert k' start' cert'
  let a := stepGraph raw least out k prior c ty start cert
  let b := stepGraph raw least out k' prior c ty start' cert'
  have ha : Derivation body [a] a := Derivation.hypothesis List.mem_cons_self
  have hb : Derivation body [b] b := Derivation.hypothesis List.mem_cons_self
  obtain ⟨forward⟩ := moveUnused raw least out prior c ty k start cert k' start' cert' ⟨ha⟩
  obtain ⟨backward⟩ := moveUnused raw least out prior c ty k' start' cert' k start cert ⟨hb⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction backward)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateThinProof
