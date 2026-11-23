module

public import LogicLineages.NativeModule.PersistentMarking.ConditionalJGuardTargets
public import LogicLineages.NativeModule.PersistentMarking.ConditionalJNilCarrierProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

/-! Proof of the frozen `ConditionalJGuardTargets` (sha256 4987b507…ec3e).  The statements concern
the guarded checker `guardedDirect d`, a different but equally admissible program; see the
targets' docstring. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.ConditionalJGuardProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules ID1Completion.SourcePresentation
open ID1Completion.InternalControlGraph (programGraph)
open ID1Completion.InternalGraphComposition (graph)
open ID1Completion.InternalTagArithmeticSyntaxProof (OTerm z suc eqn zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowFormulaCalibrationTargets NumberedWindowPresentationCheckers
open NumberedWindowArithmeticScalarTargets (fixed)
open ConditionalJUnionTargets ConditionalJSingletonTargets ConditionalJGuardTargets
open ConditionalJUnionProof (D hyp existsElim)

/-- The original algorithm rejects every replacement step out of the empty code. -/
theorem directAtZero (scalar : Nat → Bool) (positive : Nat → Nat → Nat → Bool) (cert dst : Nat) :
    NumberedWindowDirectAlgorithm.direct scalar positive 0 cert dst = false := by
  have h0 : NumberedWindowFieldAlgorithm.unpack 0 = some [] := rfl
  unfold NumberedWindowDirectAlgorithm.direct
  rw [h0]
  cases hw : NumberedWindowDirectAlgorithm.readWitness cert with
  | none => rfl
  | some w =>
    cases hy : NumberedWindowFieldAlgorithm.unpack dst with
    | none => rfl
    | some ys =>
      obtain ⟨kept, removed, added⟩ := w
      cases removed with
      | nil => simp [NumberedWindowDirectAlgorithm.directLists]
      | cons h t => simp [NumberedWindowDirectAlgorithm.directLists, List.nil_perm]

theorem exact_GuardEvaluates : GuardEvaluates := by
  intro S K i j r d ev
  refine ⟨ev.1, ev.2.1, ev.2.2.1, fun x cert y => ?_⟩
  rw [guardedDirect, ID1Completion.InternalAcceptanceCalibrationProof.evalBranch]
  have hp : evaluate (Program.projection 0) (x ::ᵥ cert ::ᵥ y ::ᵥ List.Vector.nil) = x := rfl
  have hz : evaluate (ID1Completion.InternalAcceptance.constantZero 3)
      (x ::ᵥ cert ::ᵥ y ::ᵥ List.Vector.nil) = 0 := rfl
  rw [hp, hz]
  split_ifs with hx
  · subst hx
    change 0 = (NumberedWindowDirectAlgorithm.direct _ _ 0 cert y).toNat
    rw [directAtZero]
    rfl
  · exact ev.2.2.2 x cert y

variable {body : Positive (Fin 1)}

/-- Internal rejection: the guarded supplied certificate graph at source 0 never outputs 1. -/
theorem rejectsAtZero {α : Type} {Γ : List (Formula α)} (p : Program 3) (cc s yy ww : OTerm α)
    (hs : D body Γ (eqn s z))
    (h : D body Γ (programGraph (NumberedWindowCheckerCoordinates.suppliedCertificate (guardedDirect p))
      (suc z) ![cc, s, yy, ww])) :
    D body Γ ⊥ := by
  unfold NumberedWindowCheckerCoordinates.suppliedCertificate at h
  refine ID1Completion.InternalAcceptanceSupportProof.programCompositionCases (guardedDirect p) _ (suc z) _ ⊥ h ?_
  intro β j ys Δ hj hgraph hcomp
  change D body Δ ⊥
  have h0 := hcomp 0
  change D body Δ (programGraph (Program.projection 1) (ys 0)
    (fun a => (![cc, s, yy, ww] a).relabel j)) at h0
  have e0 : D body Δ (eqn (s.relabel j) (ys 0)) := by
    unfold programGraph at h0
    rw [ID1Completion.InternalRecursionFreeInitialProof.actualInitialGraphInstances.2.2,
      ID1Completion.InternalSourceInversionSupportProof.onEquality] at h0
    exact h0
  have hs' := ID1Completion.InternalGraphCompositionFunctionalityProof.renameInto hs j Δ hj
  rw [ID1Completion.InternalTagArithmeticSyntaxProof.eqnRelabel, zRelabel] at hs'
  obtain ⟨e0⟩ := e0
  obtain ⟨hs'⟩ := hs'
  have hy : D body Δ (eqn (ys 0) z) :=
    ⟨ID1Completion.InternalTagArithmeticSupportProof.trans (ID1Completion.InternalTagArithmeticSupportProof.symm e0) hs'⟩
  have hc : D body Δ (programGraph (Program.projection 0) z ys) :=
    ID1Completion.InternalControlGraphSupportProof.outputTransport _ (ys 0) z ys hy
      (ID1Completion.InternalControlGraphSupportProof.projectionValue 0 ys)
  rw [sucRelabel, zRelabel] at hgraph
  have hzero := ID1Completion.InternalAcceptanceBranchProof.zeroBranchElim (Program.projection 0)
    (ID1Completion.InternalAcceptance.constantZero 3) p (suc z) ys hc hgraph
  have hq : D body Δ (programGraph (ID1Completion.InternalAcceptance.constantZero 3) z ys) :=
    ID1Completion.InternalAcceptanceConjunctionProof.constantZeroValue ys
  obtain ⟨e⟩ := ID1Completion.InternalControlGraphSupportProof.valueUnique
    (ID1Completion.InternalAcceptance.constantZero 3) (suc z) z ys hzero hq
  exact ⟨ID1Completion.InternalTagArithmeticSupportProof.sucNeZeroApply e⟩

theorem exact_GuardNilNoStep : GuardNilNoStep := by
  intro i j r d c α Γ y e
  rw [ID1Completion.InternalAccessibilityRulesSyntaxProof.edgeExists] at e
  refine existsElim (ψ := ⊥) e ?_
  change D _ _ ⊥
  let C := certificate (NumberedWindowInternalPresentationTargets.data i j r (guardedDirect d)) true c
    ((OrdinaryArithmetic.zeroTerm : OTerm α).relabel Sum.inl) (y.relabel Sum.inl) (.var (.inr (0 : Fin 1)))
  have h : D (sourceBody (NumberedWindowInternalPresentationTargets.data i j r (guardedDirect d)) c)
      (C :: Γ.map weaken) C := hyp C
  have hs : D (sourceBody (NumberedWindowInternalPresentationTargets.data i j r (guardedDirect d)) c)
      (C :: Γ.map weaken) (eqn ((OrdinaryArithmetic.zeroTerm : OTerm α).relabel Sum.inl) z) := by
    rw [zRelabel]
    exact ⟨ID1Completion.InternalTagArithmeticSupportProof.refl z⟩
  exact rejectsAtZero d _ _ _ _ hs h

theorem exact_GuardedJSingleton : GuardedJSingleton := by
  intro S K i j r d ev c u sg hCU hMS hSC hDG
  exact ConditionalJNilCarrierProof.exact_ActualJSingleton S K i j r (guardedDirect d)
    (exact_GuardEvaluates S K i j r d ev) c u sg hCU hMS hSC (exact_GuardNilNoStep i j r d c) hDG

theorem exact_GuardedJMembers : GuardedJMembers := by
  intro S K i j r d ev c u mem sg hCU hMS hSC hDG hMG
  exact ConditionalJNilCarrierProof.exact_ActualJMembers S K i j r (guardedDirect d)
    (exact_GuardEvaluates S K i j r d ev) c u mem sg hCU hMS hSC (exact_GuardNilNoStep i j r d c) hDG hMG

#print axioms exact_GuardEvaluates
#print axioms exact_GuardNilNoStep
#print axioms exact_GuardedJSingleton
#print axioms exact_GuardedJMembers

end LogicLineages.PersistentMarking.ConditionalJGuardProof
