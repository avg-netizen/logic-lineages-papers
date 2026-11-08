module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceAssemblyTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceRelationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceGroundProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceRelationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSourceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceDispatchEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceAssemblyClosureProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalOriginalObjectFiberSourceAssembly InternalOriginalObjectFiberSourceAssemblyTargets
open InternalPositiveUnfoldingSupportProof InternalRecursionClosureLogicProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Only closed type codes are evaluated by the concrete cons program. -/
theorem arrowEvaluation (sigma tau : Ty) :
    evaluate InternalOriginalObjectFiberSourceDispatch.arrow
      (List.Vector.ofFn ![typeNumber sigma,typeNumber tau]) = typeNumber (.arrow sigma tau) := by
  rw [InternalOriginalObjectFiberSourceDispatchEvaluationProof.actualOriginalObjectSourceAuxiliaryCalibration.2.2.2]
  rfl

theorem actualInternalOriginalObjectAssemblyTypedClosure :
    ActualInternalOriginalObjectAssemblyTypedClosure := by
  intro K Gamma p context hw body α Delta typ x y
  let P := GuardedSource.literalTyped (comp K Gamma p) context typ x ⊓
    GuardedSource.literalR (src K Gamma p) context x y
  obtain ⟨d⟩ := GuardedSourceRelationProof.relationClosure
    (body := body) (Gamma := P :: Delta)
    (GammaGuardedSource.baseSource (patchedSource K Gamma p)
      InternalOriginalObjectFiberSourceDispatch.gamma)
    (GammaGuardedSource.baseComputability (patchedComp K Gamma p)
      InternalOriginalObjectFiberSourceDispatch.valid InternalOriginalObjectFiberSourceDispatch.gamma)
    InternalOriginalObjectFiberSourceDispatch.tag p.window context hw typ x y
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  exact ⟨Derivation.implicationIntroduction d⟩

theorem actualInternalOriginalObjectAssemblyGroundClosure :
    ActualInternalOriginalObjectAssemblyGroundClosure := by
  intro K Gamma p context hw α Delta x y
  rw [GuardedSourceGroundProof.groundFormula (comp K Gamma p) context α x,
    GuardedSourceGroundProof.groundFormula (comp K Gamma p) context α y]
  obtain ⟨dt⟩ := actualInternalOriginalObjectAssemblyTypedClosure K Gamma p context hw
    (SourcePresentation.sourceBody (src K Gamma p) context) α []
    (numeral (typeNumber .ground)) x y
  obtain ⟨ds⟩ := GuardedSourceGroundProof.scalarDownward (src K Gamma p) context α x y
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  let P := (GuardedSource.literalTyped (comp K Gamma p) context (numeral (typeNumber .ground)) x ⊓
    GuardedSourceGround.literalGround x) ⊓ GuardedSource.literalR (src K Gamma p) context x y
  have hp : Derivation (SourcePresentation.sourceBody (src K Gamma p) context) (P :: Delta) P :=
    Derivation.hypothesis List.mem_cons_self
  have htx := Derivation.conjunctionLeft (Derivation.conjunctionLeft hp)
  have hgx := Derivation.conjunctionRight (Derivation.conjunctionLeft hp)
  have hr := Derivation.conjunctionRight hp
  exact Derivation.conjunctionIntroduction
    (Derivation.implicationElimination (weakenClosed dt _)
      (Derivation.conjunctionIntroduction htx hr))
    (Derivation.implicationElimination (weakenClosed ds _)
      (Derivation.conjunctionIntroduction hgx hr))

theorem actualInternalOriginalObjectAssemblyGuardTransport :
    ActualInternalOriginalObjectAssemblyGuardTransport := by
  intro K Gamma p context body α Delta typ x y u
  let P := ((GuardedSource.literalTyped (comp K Gamma p) context typ x ⊓
    GuardedSource.literalR (src K Gamma p) context x y) ⊓
    GammaGuardedSource.literalGuard (comp K Gamma p) y u)
  have h : Derivation body (P :: Delta) P := Derivation.hypothesis List.mem_cons_self
  obtain ⟨d⟩ := GammaGuardedSourceRelationProof.relationTransport
    (patchedSource K Gamma p) (patchedComp K Gamma p)
    InternalOriginalObjectFiberSourceDispatch.valid InternalOriginalObjectFiberSourceDispatch.gamma
    InternalOriginalObjectFiberSourceDispatch.tag p.window context typ x y u
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionLeft h)⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionLeft h)⟩
    ⟨Derivation.conjunctionRight h⟩
  exact ⟨Derivation.implicationIntroduction d⟩

theorem actualInternalOriginalObjectAssemblyApplicationTotality :
    ActualInternalOriginalObjectAssemblyApplicationTotality := by
  intro K Gamma p context hw body α Delta sigma tau f a
  obtain ⟨d⟩ := ApplicationGuardedApplicationProof.actualOriginalTotality
    body (baseComp K Gamma p) p.window InternalOriginalObjectFiberSourceDispatch.arrow
    (patchedResult K Gamma p) context sigma tau hw (arrowEvaluation sigma tau) α f a
  exact ⟨weakenClosed d Delta⟩

theorem actualInternalOriginalObjectAssemblyApplicationFunctionality :
    ActualInternalOriginalObjectAssemblyApplicationFunctionality := by
  intro K Gamma p context hw body α Delta sigma tau f a out other
  obtain ⟨d⟩ := ApplicationGuardedApplicationProof.actualOriginalFunctionality
    body (baseComp K Gamma p) p.window InternalOriginalObjectFiberSourceDispatch.arrow
    (patchedResult K Gamma p) context sigma tau hw (arrowEvaluation sigma tau) α f a out other
  exact ⟨weakenClosed d Delta⟩

theorem actualInternalOriginalObjectAssemblyApplicationComputability :
    ActualInternalOriginalObjectAssemblyApplicationComputability := by
  intro K Gamma p context hw body α Delta sigma tau f a out
  obtain ⟨d⟩ := closedApply
    (InternalComputabilityApplicationProof.actualOriginalApplicationComputability
      body (baseComp K Gamma p) p.window InternalOriginalObjectFiberSourceDispatch.arrow
      (patchedResult K Gamma p) α sigma tau (numeral context) f a out)
    (InternalComputabilityApplicationSourceProof.closedMetadata p.window
      InternalOriginalObjectFiberSourceDispatch.arrow context sigma tau hw (arrowEvaluation sigma tau))
  exact ⟨weakenClosed d Delta⟩

theorem actualInternalOriginalObjectAssemblyResultComputability :
    ActualInternalOriginalObjectAssemblyResultComputability := by
  intro K Gamma p context hw body α Delta sigma tau f a out
  obtain ⟨d⟩ := closedApply
    (InternalComputabilityApplicationProof.actualOriginalResultComputability
      body (baseComp K Gamma p) p.window InternalOriginalObjectFiberSourceDispatch.arrow
      (patchedResult K Gamma p) α sigma tau (numeral context) f a out)
    (InternalComputabilityApplicationSourceProof.closedMetadata p.window
      InternalOriginalObjectFiberSourceDispatch.arrow context sigma tau hw (arrowEvaluation sigma tau))
  exact ⟨weakenClosed d Delta⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceAssemblyClosureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceAssemblyClosureProof
