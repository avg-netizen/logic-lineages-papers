module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxEdgeOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFunctionGuardFieldsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEnrichedEdgeReversalProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxEdgeCasesOpenProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalControlGraphSupportProof (projectionValue)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchElim)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalLiteralFunctionGuardFieldsProof (nodeAtCases)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalLiteralEnrichedEdgeReversalProof (edgeRename)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralTypedAuxEdgeGuardProof
open NumberedWindowInternalLiteralTypedAuxEdgeSlotsProof
open NumberedWindowInternalLiteralTypedAuxEdgeOpenProof

attribute [local irreducible] programGraph
variable {T : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem auxRowRename {β : Type} (p : AuxRow α) (j : α → β) : p.term.relabel j = (p.map j).term := by
  simp only [AuxRow.term,AuxRow.map,auxiliaryRename]

theorem exact_OpenAuxShapeCases (q : OTerm α) (goal : Formula α) (held : D T Γ (unary termShape (suc z) q))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (p : AuxRow β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) → D T Δ (eqn (q.relabel j) p.term) → D T Δ (goal.relabel j)) :
    D T Γ goal := by
  have shape := onTape termShape 0 (suc z) (![q,z,z] : Fin 3 → OTerm α) held
  apply nodeAtCases 6 4 0 (![q,z,z] : Fin 3 → OTerm α) goal shape
  intro β j Δ ls keep count formula _
  rcases ls with _ | ⟨a,_ | ⟨b,_ | ⟨c,_ | ⟨d,_ | ⟨e,es⟩⟩⟩⟩⟩ <;> simp at count
  exact use β j Δ ⟨a,b,c,d⟩ keep formula

theorem exact_OpenAuxEdgeTargetShape (B E : Program 4) (ctx ty q r : OTerm α)
    (accepted : D T Γ (acceptEdge (typedAuxEdgeGuard B E) ctx ty q r))
    (source : D T Γ (unary termShape (suc z) q)) :
    D T Γ (unary termShape (suc z) r) := by
  let xs : Fin 4 → OTerm α := ![ctx,ty,q,r]
  obtain ⟨outer⟩ := conjunctionRecover B (auxChildGuard E) xs accepted
  have positive := exact_OpenEdgeSlotRead termShape 2 xs (suc z) source
  have checked := successorBranchElim (readSlot termShape 2) (constantOne 4)
    (validateAuxiliary E) (suc z) z xs positive ⟨Derivation.conjunctionRight outer⟩
  obtain ⟨parts⟩ := conjunctionRecover (readSlot termShape 3)
    (conjunction (sameField 0) (conjunction (sameField 1) (chooseChild E))) xs checked
  apply compositionRecover termShape (Fin.cons (.projection 3) Fin.elim0) (suc z) xs ![r]
    ⟨Derivation.conjunctionLeft parts⟩
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 3 xs

theorem exact_OpenRetapePackedEdge (E : Program 4) (ctx ty q r q' r' : OTerm α)
    (a : D T Γ (eqn q q')) (b : D T Γ (eqn r r'))
    (held : D T Γ (acceptEdge E ctx ty q r)) : D T Γ (acceptEdge E ctx ty q' r') := by
  change D T Γ (programGraph E (suc z) ![ctx,ty,q,r]) at held
  change D T Γ (programGraph E (suc z) ![ctx,ty,q',r'])
  unfold programGraph at *
  apply graphInputTransport T α 4 Γ (OrdinaryArithmetic.graphFormula E) (suc z)
    ![ctx,ty,q,r] ![ctx,ty,q',r'] _ held
  intro i
  rw [onEquality]
  exact Fin.cases (⟨refl ctx⟩ : D T Γ (eqn ctx ctx)) (Fin.cases (⟨refl ty⟩ : D T Γ (eqn ty ty))
    (Fin.cases a (Fin.cases b (fun n => Fin.elim0 n)))) i

/-- Open the physically admitted child alternative on arbitrary raw
endpoints. A true source auxiliary guard supplies the corresponding
true target shape and both literal rows on the same accepted edge. -/
theorem exact_OpenAnyTypedAuxEdgeCases (B E : Program 4) (ctx ty q r : OTerm α) (goal : Formula α)
    (held : D T Γ (acceptEdge (typedAuxEdgeGuard B E) ctx ty q r))
    (source : D T Γ (unary termShape (suc z) q))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (a b : AuxRow β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D T Δ (eqn (q.relabel j) a.term) → D T Δ (eqn (r.relabel j) b.term) →
      D T Δ (eqn a.dom b.dom ⊓ (eqn a.cod b.cod ⊓ childAlternatives E (ctx.relabel j) a b)) →
      D T Δ (goal.relabel j)) : D T Γ goal := by
  have target := exact_OpenAuxEdgeTargetShape B E ctx ty q r held source
  apply exact_OpenAuxShapeCases q goal source
  intro β j Δ a keep qa
  have peer := renameInto target j Δ keep
  simp only [NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof.unaryRename,
    ID1Completion.InternalTagArithmeticSyntaxProof.sucRelabel,ID1Completion.InternalTagArithmeticSyntaxProof.zRelabel] at peer
  have old := renameInto held j Δ keep
  rw [edgeRename] at old
  apply exact_OpenAuxShapeCases (r.relabel j) (goal.relabel j) peer
  intro γ k Θ b stay rb
  let new := k ∘ j
  have keeps (φ : Formula α) (inΓ : φ ∈ Γ) : φ.relabel new ∈ Θ := by
    simpa only [new,formulaRelabelComposition] using stay _ (keep φ inΓ)
  have accepts := renameInto old k Θ stay
  rw [edgeRename] at accepts
  have qa' := renameInto qa k Θ stay
  rw [eqnRelabel,auxRowRename] at qa'
  have retaped := exact_OpenRetapePackedEdge (typedAuxEdgeGuard B E)
    ((ctx.relabel j).relabel k) ((ty.relabel j).relabel k)
    ((q.relabel j).relabel k) ((r.relabel j).relabel k) (a.map k).term b.term qa' rb accepts
  have inner := exact_OpenTypedAuxEdgeRows B E ((ctx.relabel j).relabel k)
    ((ty.relabel j).relabel k) (a.map k) b retaped
  have done := use γ new Θ (a.map k) b keeps
    (by simpa only [new,Term.relabel_relabel] using qa')
    (by simpa only [new,Term.relabel_relabel] using rb)
    (by simpa only [new,Term.relabel_relabel] using inner)
  simpa only [new,formulaRelabelComposition] using done

#print axioms exact_OpenAuxShapeCases
#print axioms exact_OpenAuxEdgeTargetShape
#print axioms exact_OpenRetapePackedEdge
#print axioms exact_OpenAnyTypedAuxEdgeCases
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxEdgeCasesOpenProof
