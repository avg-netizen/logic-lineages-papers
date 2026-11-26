module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementObjectTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementObjectRecognitionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementObjectBranchProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue programRename equalEqn)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open ID1Completion.InternalAcceptance (branch conjunction)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalProbeTargets (OTerm)
open NumberedWindowInternalAtomicRefinement (atSource atTarget bottomTarget bottomOf bottomEmitter)
open NumberedWindowInternalAtomicRefinementObjectTargets (packedBottomTerm sourceFields)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (bottomEmitterGraph)
open NumberedWindowInternalAtomicApplicationShapeObjectControlProof (callSlot)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalFreshProbeDispatchProgram (compareNumbers)
open NumberedWindowInternalFreshProbeParsedEmitter (rawContext rawResult)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalAuxBottomRefinement NumberedWindowInternalAuxBottomRefinementObjectTargets
open NumberedWindowInternalAuxBottomRefinementObjectRecognitionProof (exactRecognition)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem branchAST (i : Program 1) (r : Program 3) :
    refineAuxBottom i r = branch (atSource sourceFlag) r (acceptedTerminal i r) := by
  rw [refineAuxBottom,exact_DispatchControlAST.2.2.2.2.1]

section
attribute [local irreducible] programGraph

private theorem terminalParts (i : Program 1) (r : Program 3) (xs : Fin 3 → OTerm α)
    (h : Nonempty (Derivation B Γ (programGraph (acceptedTerminal i r) (suc z) xs))) :
    Nonempty (Derivation B Γ
      (programGraph r (suc z) xs ⊓
        programGraph (conjunction bottomTarget (atTarget i)) (suc z) xs)) := by
  rw [acceptedTerminal,exact_DispatchControlAST.2.2.2.2.2,exact_DispatchControlAST.2.2.2.2.2] at h
  exact conjunctionRecover r (conjunction bottomTarget (atTarget i)) xs h

private theorem reportBottom (x c t : OTerm α)
    (h : Nonempty (Derivation B Γ (sourceFields x c t))) :
    Nonempty (Derivation B Γ (programGraph bottomOf (packedBottomTerm c t) ![x])) := by
  obtain ⟨f⟩ := h
  have hc : Nonempty (Derivation B Γ (programGraph rawContext c ![x])) :=
    ⟨Derivation.conjunctionLeft f⟩
  have ht : Nonempty (Derivation B Γ (programGraph rawResult t ![x])) :=
    ⟨Derivation.conjunctionRight f⟩
  unfold bottomOf
  apply compositionValue bottomEmitter (Fin.cons rawContext (Fin.cons rawResult Fin.elim0))
    (packedBottomTerm c t) ![x] ![c,t] (bottomEmitterGraph c t)
  intro k
  exact Fin.cases hc (Fin.cases ht (fun j => Fin.elim0 j)) k

private theorem checkedTarget (x w y c t : OTerm α)
    (fields : Nonempty (Derivation B Γ (sourceFields x c t)))
    (h : Nonempty (Derivation B Γ (programGraph bottomTarget (suc z) ![x,w,y]))) :
    Nonempty (Derivation B Γ (equal y (packedBottomTerm c t))) := by
  let xs : Fin 3 → OTerm α := ![x,w,y]
  let b := packedBottomTerm c t
  let ps : Fin 2 → Program 3 := Fin.cons (.projection (2 : Fin 3)) (Fin.cons (atSource bottomOf) Fin.elim0)
  have new : Nonempty (Derivation B Γ (programGraph (atSource bottomOf) b xs)) :=
    callSlot bottomOf 0 b xs (reportBottom x c t fields)
  have tested := compositionRecover compareNumbers ps (suc z) xs ![y,b] h
    (fun j => Fin.cases (projectionValue (2 : Fin 3) xs) (Fin.cases new (fun k => Fin.elim0 k)) j)
  rw [exact_DispatchControlAST.2.2.2.1] at tested
  rw [equalEqn]
  exact equalityOfAcceptance y b tested

private theorem carryActual (i : Program 1) (x w y : OTerm α)
    (h : Nonempty (Derivation B Γ (programGraph (atTarget i) (suc z) ![x,w,y]))) :
    Nonempty (Derivation B Γ (programGraph i (suc z) ![y])) := by
  let xs : Fin 3 → OTerm α := ![x,w,y]
  unfold atTarget at h
  apply compositionRecover i (fun _ : Fin 1 => .projection (2 : Fin 3)) (suc z) xs ![y] h
  intro j
  obtain rfl := Fin.eq_zero j
  exact projectionValue (2 : Fin 3) xs

theorem exactTerminal : ExactOpenAuxBottomTerminal := by
  intro i r B α Γ x w y c dom cod stored arg shape accepted
  let xs : Fin 3 → OTerm α := ![x,w,y]
  obtain ⟨source⟩ := exactRecognition B α Γ x c dom cod stored arg shape
  have on : Nonempty (Derivation B Γ (programGraph (atSource sourceFlag) (suc z) xs)) :=
    callSlot sourceFlag 0 (suc z) xs ⟨Derivation.conjunctionLeft source⟩
  change Nonempty (Derivation B Γ (programGraph (refineAuxBottom i r) (suc z) xs)) at accepted
  rw [branchAST] at accepted
  have yes := successorBranchElim (atSource sourceFlag) r (acceptedTerminal i r) (suc z) z xs on accepted
  obtain ⟨done⟩ := terminalParts i r xs yes
  obtain ⟨facts⟩ := conjunctionRecover bottomTarget (atTarget i) xs ⟨Derivation.conjunctionRight done⟩
  obtain ⟨dest⟩ := checkedTarget x w y c cod ⟨Derivation.conjunctionRight source⟩
    ⟨Derivation.conjunctionLeft facts⟩
  obtain ⟨carrier⟩ := carryActual i x w y ⟨Derivation.conjunctionRight facts⟩
  exact ⟨Derivation.conjunctionIntroduction dest carrier⟩

theorem forgets : ExactOpenAuxBottomForgets := by
  intro i r B α Γ x w y accepted
  let xs : Fin 3 → OTerm α := ![x,w,y]
  change Nonempty (Derivation B Γ (programGraph (refineAuxBottom i r) (suc z) xs)) at accepted
  change Nonempty (Derivation B Γ (programGraph r (suc z) xs))
  rw [branchAST] at accepted
  apply optionGraphCases (atSource sourceFlag) xs (programGraph r (suc z) xs)
  · intro β j Δ hJ hz
    have moved := renameInto accepted j Δ hJ
    simp only [programRename,sucRelabel,zRelabel] at moved ⊢
    exact zeroBranchElim (atSource sourceFlag) r (acceptedTerminal i r) (suc z) _ hz moved
  · intro β j Δ v hJ hs
    have moved := renameInto accepted j Δ hJ
    simp only [programRename,sucRelabel,zRelabel] at moved ⊢
    let ys : Fin 3 → OTerm β := fun k => (xs k).relabel j
    have inside := successorBranchElim (atSource sourceFlag) r (acceptedTerminal i r) (suc z) v ys hs moved
    obtain ⟨both⟩ := terminalParts i r ys inside
    exact ⟨Derivation.conjunctionLeft both⟩

end

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementObjectBranchProof
