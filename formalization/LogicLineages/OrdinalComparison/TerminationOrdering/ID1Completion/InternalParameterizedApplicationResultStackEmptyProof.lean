module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackWiringProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionStateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationLawsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackEmptyProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalGraphComposition
open InternalApplicationCertificateConstructors InternalParameterizedApplicationResultStack
open InternalParameterizedApplicationResultStackWiringProof
open InternalApplicationResultStackCompositionStateProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof InternalGraphCompositionFunctionalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The original empty-state graph exposes status one and work zero. The
binary AST therefore returns input 0, independently of the unchanged p. -/
theorem emptyFixed (guard leaf : Program 2) (combine : Program 5)
    (results state parameter : OTerm α)
    (hs : Nonempty (Derivation body Gamma
      (graph1 InternalApplicationResultStack.emptyState state results))) :
    Nonempty (Derivation body Gamma
      (graph2 (transitionP guard leaf combine) state state parameter)) := by
  let ss : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  let xs : Fin 2 → OTerm α := Fin.cons state (Fin.cons parameter Fin.elim0)
  have hl := emptyAsLive state results hs
  have hstatus := sameAccept InternalApplicationResultStack.status (InternalLessThan.constantOne 1)
    (suc z) ss (liveStatus state z results hl) (InternalLessThanSupportProof.oneConstantValue ss)
  have hwork := andLeft (liveStateFields state z results hl)
  apply successorBranchIntro _ _ _ state z xs
    (liftValue (InternalApplicationValidityStack.exactOne InternalApplicationResultStack.status)
      (suc z) state parameter hstatus)
  exact zeroBranchIntro _ _ _ state xs
    (liftValue InternalApplicationResultStack.work z state parameter hwork) (projectionValue 0 xs)

theorem actualOriginalParameterizedApplicationResultStackEmpty :
    InternalParameterizedApplicationResultStackTargets.ActualOriginalParameterizedApplicationResultStackEmpty := by
  intro body guard leaf combine α Gamma results state out parameter
  let c := graph1 InternalApplicationResultStack.emptyState state results
  let g := graph2 (transitionP guard leaf combine) out state parameter
  let r := equal out state
  have hc₁ : Nonempty (Derivation body (g :: c :: Gamma) c) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hc₂ : Nonempty (Derivation body (r :: c :: Gamma) c) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := valueUnique (transitionP guard leaf combine) out state
    (Fin.cons state (Fin.cons parameter Fin.elim0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
    (emptyFixed guard leaf combine results state parameter hc₁)
  have heq : Nonempty (Derivation body (r :: c :: Gamma) (eqn state out)) := by
    have hr : Derivation body (r :: c :: Gamma) r := Derivation.hypothesis List.mem_cons_self
    have hr' : Derivation body (r :: c :: Gamma) (eqn out state) := by
      simpa only [r,equalEqn] using hr
    exact ⟨symm hr'⟩
  obtain ⟨hb⟩ := outputTransport (transitionP guard leaf combine) state out
    (Fin.cons state (Fin.cons parameter Fin.elim0)) heq
    (emptyFixed guard leaf combine results state parameter hc₂)
  have hf' : Derivation body (g :: c :: Gamma) r := by simpa only [r,equalEqn] using hf
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf') (Derivation.implicationIntroduction hb))⟩

/-- The accepted actual parameterized fixed-point law acts on the whole
original state. No worklist induction, framing, or full-run claim is used. -/
theorem actualOriginalParameterizedApplicationResultStackTerminalIteration :
    InternalParameterizedApplicationResultStackTargets.ActualOriginalParameterizedApplicationResultStackTerminalIteration := by
  intro body guard leaf combine α Gamma results state out count parameter
  let c := graph1 InternalApplicationResultStack.emptyState state results
  have hc : Nonempty (Derivation body (c :: Gamma) c) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hf⟩ := emptyFixed guard leaf combine results state parameter hc
  obtain ⟨hi⟩ := InternalParameterizedNumericIterationLawsProof.actualOriginalParameterizedNumericIterationFixedPoint
    body (transitionP guard leaf combine) α (c :: Gamma) out count state parameter
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hi hf)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackEmptyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackEmptyProof
