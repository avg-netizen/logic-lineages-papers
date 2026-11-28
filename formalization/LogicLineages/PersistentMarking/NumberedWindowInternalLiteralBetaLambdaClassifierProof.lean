module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAlignedBetaTargetProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaAcceptedChildProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaBodyShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaLambdaClassifierProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalBoundedDescentNormalizerStepSupportProof (conjunctionReject)
open ID1Completion.InternalControlGraphChoiceProof (excludedMiddle)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelope (nodeGood)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralBetaLeafProof (rawLambdaShape)
open NumberedWindowInternalLiteralBetaLeafOpenProof (rawLambdaTerm)
open NumberedWindowInternalLiteralBetaBodyShapeProof (exact_OpenBetaLambdaBodyShape)
open NumberedWindowInternalLiteralBetaOperandAlignmentProof (AlignedBetaRow)
open NumberedWindowInternalLiteralAlignedBetaTargetProof
  (exact_OpenAlignedBetaRowRename exact_OpenAlignedBetaTarget)
open NumberedWindowInternalLiteralSingletonDepthNumericProof (zeroDepthInstance)
open NumberedWindowInternalLiteralSingletonLambdaMachineProof (singletonLambda)
open NumberedWindowInternalLiteralSingletonLambdaAcceptedChildProof
  (rawLambdaTermRename exact_OpenAcceptedBetaLambdaChild)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Split on the literal lambda selector of the installed instance. A
hit supplies the decoded body, the successful child computation, and
the rebuilt target in one continuation. A miss supplies selector zero. -/
theorem exact_OpenAcceptedBetaLambdaCases (V : Program 1) (H : Program 2) (U : Program 3)
    (a body r : OTerm α) (goal : Formula α)
    (held : D B Γ (programGraph (zeroDepthInstance (singletonLambda V H U))
      (suc r) ![a,body]))
    (other : D B (unary rawLambdaShape z body :: Γ) goal)
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (ty b u : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (eqn (body.relabel j) (rawLambdaTerm ty b)) →
      D B Δ (programGraph U (suc u) ![a.relabel j,suc z,b]) →
      D B Δ (eqn (suc (r.relabel j)) (suc (rawLambdaTerm ty u))) →
      D B Δ (goal.relabel j)) : D B Γ goal := by
  let test := unary rawLambdaShape (suc z) body
  have yes : D B (test :: Γ) goal := by
    apply exact_OpenBetaLambdaBodyShape body goal ⟨Derivation.hypothesis List.mem_cons_self⟩
    intro β j Δ ty b keep shape
    have keepΓ (f : Formula α) (mem : f ∈ Γ) : f.relabel j ∈ Δ :=
      keep f (List.mem_cons_of_mem _ mem)
    have accepted : D B Δ (programGraph (zeroDepthInstance (singletonLambda V H U))
        (suc (r.relabel j)) ![a.relabel j,body.relabel j]) := by
      simpa only [programRename,binaryInputsRename,sucRelabel] using renameInto held j Δ keepΓ
    apply exact_OpenAcceptedBetaLambdaChild V H U (a.relabel j) (body.relabel j) ty b
      (r.relabel j) (goal.relabel j) shape accepted
    intro γ k Θ u stay child rebuilt
    have keepBoth (f : Formula α) (mem : f ∈ Γ) : f.relabel (k ∘ j) ∈ Θ := by
      simpa only [formulaRelabelComposition] using stay _ (keepΓ f mem)
    have bodyEq : D B Θ (eqn (body.relabel (k ∘ j)) (rawLambdaTerm (ty.relabel k) (b.relabel k))) := by
      simpa only [eqnRelabel,rawLambdaTermRename,Term.relabel_relabel] using
        renameInto shape k Θ stay
    rw [formulaRelabelComposition]
    exact use γ (k ∘ j) Θ (ty.relabel k) (b.relabel k) u keepBoth bodyEq
      (by simpa only [Term.relabel_relabel] using child)
      (by simpa only [Term.relabel_relabel] using rebuilt)
  have no : D B (test.not :: Γ) goal := by
    have zero : D B (test.not :: Γ) (unary rawLambdaShape z body) := by
      unfold unary rawLambdaShape nodeGood
      apply conjunctionReject
      exact ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨zero⟩ := zero
    obtain ⟨other⟩ := other
    exact ⟨Derivation.implicationElimination (addHyp (Derivation.implicationIntroduction other) test.not)
      zero⟩
  obtain ⟨yes⟩ := yes
  obtain ⟨no⟩ := no
  exact ⟨disjunctionElimination (excludedMiddle test)
    (Derivation.implicationIntroduction yes) (Derivation.implicationIntroduction no)⟩

/-- On the lambda branch the actual aligned target least report is retaped
to the rebuilt code, at the original context, type, and least element. -/
theorem exact_OpenAlignedBetaLambdaCases (L₀ L : Program 3)
    (V : Program 1) (H : Program 2) (U : Program 3)
    (ctx dom cod fn arg sc st after q r d e f a bind body y : OTerm α)
    (goal : Formula α)
    (row : AlignedBetaRow L₀ L (zeroDepthInstance (singletonLambda V H U))
      B Γ ctx dom cod fn arg sc st after q r d e f a bind body y)
    (other : D B (unary rawLambdaShape z body :: Γ) goal)
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (ty b u : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (eqn (body.relabel j) (rawLambdaTerm ty b)) →
      D B Δ (programGraph U (suc u) ![a.relabel j,suc z,b]) →
      D B Δ (eqn (r.relabel j) (rawLambdaTerm ty u)) →
      D B Δ (programGraph L (suc (after.relabel j)) ![sc.relabel j,st.relabel j,rawLambdaTerm ty u]) →
      D B Δ (eqn (y.relabel j) (addressTerm (sc.relabel j) (st.relabel j) (after.relabel j))) →
      D B Δ (goal.relabel j)) : D B Γ goal := by
  apply exact_OpenAcceptedBetaLambdaCases V H U a body r goal row.instanceRun other
  intro β j Δ ty b u keep shape child output
  have moved := exact_OpenAlignedBetaRowRename row j Δ keep
  obtain ⟨same,latest,address⟩ := exact_OpenAlignedBetaTarget (rawLambdaTerm ty u) moved output
  exact use β j Δ ty b u keep shape child same latest address

#print axioms exact_OpenAcceptedBetaLambdaCases
#print axioms exact_OpenAlignedBetaLambdaCases
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaLambdaClassifierProof
