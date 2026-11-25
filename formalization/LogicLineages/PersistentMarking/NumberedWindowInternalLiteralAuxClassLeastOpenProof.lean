module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxClassLeastProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxProfileLeastOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxClassLeastOpenProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (projectionValue compositionValue programRename valueUnique outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover constantZeroValue)
open ID1Completion.InternalBoundedDescentNormalizerStepSupportProof (conjunctionReject)
open ID1Completion.InternalControlGraphChoiceProof (excludedMiddle)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalLessThan (constantOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (D)
open NumberedWindowInternalLiteralAuxClassLeastProof

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem keepOriginal (L : Program 3) (ctx q code t : OTerm α)
    (held : D B Γ (programGraph (retainClasses L) (suc t) ![ctx,q,code])) :
    D B Γ (eqn code (suc t)) := by
  apply optionGraphCases (checkAuxiliaryClasses L) ![ctx,q,code] (eqn code (suc t))
  · intro β j Δ keep denied
    rw [tripleInputsRename] at denied
    have held' := renameInto held j Δ keep
    simp only [programRename,tripleInputsRename,sucRelabel] at held'
    let xs : Fin 3 → OTerm β := ![ctx.relabel j,q.relabel j,code.relabel j]
    have bad := zeroBranchElim (checkAuxiliaryClasses L) (constantZero 3) (.projection 2)
      (suc (t.relabel j)) xs denied held'
    obtain ⟨err⟩ := valueUnique (constantZero 3) (suc (t.relabel j)) z xs bad (constantZeroValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply err)⟩
  · intro β j Δ k keep accepted
    rw [tripleInputsRename] at accepted
    rw [eqnRelabel,sucRelabel]
    let xs : Fin 3 → OTerm β := ![ctx.relabel j,q.relabel j,code.relabel j]
    have held' := renameInto held j Δ keep
    simp only [programRename,tripleInputsRename,sucRelabel] at held'
    have v := successorBranchElim (checkAuxiliaryClasses L) (constantZero 3) (.projection 2)
      (suc (t.relabel j)) k xs accepted held'
    exact valueUnique (.projection 2) (code.relabel j) (suc (t.relabel j)) xs
      (projectionValue 2 xs) v

theorem exact_OpenLiteralAuxClassLeastReport (L : Program 3) (ctx ty q t : OTerm α)
    (held : D B Γ (programGraph (auxClassLeast L) (suc t) ![ctx,ty,q])) :
    D B Γ (programGraph L (suc t) ![ctx,ty,q] ⊓
      programGraph (retainClasses L) (suc t) ![ctx,q,suc t]) := by
  let xs : Fin 3 → OTerm α := ![ctx,ty,q]
  let select : Fin 3 → Program 3 := Fin.cons (.projection 0) (Fin.cons (.projection 2) (Fin.cons L Fin.elim0))
  have ancestor : D B Γ (programGraph L (suc t) xs) := by
    apply programCases L xs (programGraph L (suc t) xs)
    intro β j Δ k keep selected
    simp only [xs,programRename,tripleInputsRename,sucRelabel]
    simp only [xs,tripleInputsRename] at selected
    let tape : Fin 3 → OTerm β := ![ctx.relabel j,ty.relabel j,q.relabel j]
    have held' := renameInto held j Δ keep
    simp only [programRename,tripleInputsRename,sucRelabel] at held'
    have tested : D B Δ (programGraph (retainClasses L) (suc (t.relabel j)) ![ctx.relabel j,q.relabel j,k]) := by
      apply compositionRecover (retainClasses L) select (suc (t.relabel j)) tape
        ![ctx.relabel j,q.relabel j,k] held'
      exact fun i => Fin.cases (projectionValue 0 tape)
        (Fin.cases (projectionValue 2 tape) (Fin.cases selected (fun e => Fin.elim0 e))) i
    exact outputTransport L k (suc (t.relabel j)) tape
      (keepOriginal L (ctx.relabel j) (q.relabel j) k (t.relabel j) tested) selected
  have checks : D B Γ (programGraph (retainClasses L) (suc t) ![ctx,q,suc t]) := by
    apply compositionRecover (retainClasses L) select (suc t) xs ![ctx,q,suc t] held
    exact fun i => Fin.cases (projectionValue 0 xs)
      (Fin.cases (projectionValue 2 xs) (Fin.cases ancestor (fun e => Fin.elim0 e))) i
  obtain ⟨a⟩ := ancestor
  obtain ⟨b⟩ := checks
  exact ⟨Derivation.conjunctionIntroduction a b⟩

/-- Both actual child-class comparators have output unit on a
successfully guarded auxiliary least report. The shape observation
is on the actual raw input, not on a selected substitute. -/
theorem exact_OpenLiteralAuxClassTests (L : Program 3) (ctx ty q t : OTerm α)
    (held : D B Γ (programGraph (auxClassLeast L) (suc t) ![ctx,ty,q]))
    (aux : D B Γ (unary termShape (suc z) q)) :
    D B Γ (programGraph (compareChildClass (functionClass L)) (suc z) ![ctx,q,suc t] ⊓
      programGraph (compareChildClass (argumentClass L)) (suc z) ![ctx,q,suc t]) := by
  let xs : Fin 3 → OTerm α := ![ctx,q,suc t]
  let goal := programGraph (childClassesAgree L) (suc z) xs
  obtain ⟨h⟩ := exact_OpenLiteralAuxClassLeastReport L ctx ty q t held
  have yes : D B Γ (programGraph selectedAuxiliary (suc z) xs) := by
    apply compositionValue termShape (Fin.cons (.projection 1) Fin.elim0) (suc z) xs ![q] aux
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 1 xs
  have bad : D B (goal.not :: Γ) goal := by
    have denied : D B (goal.not :: Γ) goal.not := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have zero : D B (goal.not :: Γ) (programGraph (childClassesAgree L) z xs) :=
      conjunctionReject (compareChildClass (functionClass L)) (compareChildClass (argumentClass L)) xs denied
    obtain ⟨yp⟩ := yes
    have reject : D B (goal.not :: Γ) (programGraph (checkAuxiliaryClasses L) z xs) :=
      successorBranchIntro selectedAuxiliary (constantOne 3) (childClassesAgree L) z z xs ⟨addHyp yp _⟩ zero
    have impossible := zeroBranchElim (checkAuxiliaryClasses L) (constantZero 3) (.projection 2)
      (suc t) xs reject ⟨addHyp (Derivation.conjunctionRight h) _⟩
    obtain ⟨err⟩ := valueUnique (constantZero 3) (suc t) z xs impossible (constantZeroValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply err)⟩
  obtain ⟨contradiction⟩ := bad
  have success : D B Γ goal := ⟨disjunctionElimination (excludedMiddle goal)
    (Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self))
    (Derivation.implicationIntroduction contradiction)⟩
  exact conjunctionRecover (compareChildClass (functionClass L)) (compareChildClass (argumentClass L)) xs success

#print axioms exact_OpenLiteralAuxClassLeastReport
#print axioms exact_OpenLiteralAuxClassTests
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxClassLeastOpenProof
