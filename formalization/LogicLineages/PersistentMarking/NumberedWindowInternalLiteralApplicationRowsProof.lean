module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxProfileNeutralSourceProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenForwardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenFormulaProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicAddressReportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationRowsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename inputsRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalFreshProbeParsedEmitter (rawLeast)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalLiteralAtomicAddressReportProof (renameAddress)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)
open NumberedWindowInternalSparseApplicationFrontendTargets (parsedApplicationInputs)
open NumberedWindowInternalSparseApplicationFrontendOpenForwardProof (forward)
open NumberedWindowInternalSparseApplicationFrontendOpenBindingProof (rowCases)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (reportUnfold reportBinder auxiliaryRename)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (D)
open NumberedWindowInternalNeutralFactsTargets (atom)
open NumberedWindowInternalNeutralFactsSyntaxProof (atomRename)
open NumberedWindowInternalLiteralNeutralAtomProof (neutralSource)
open NumberedWindowInternalLiteralAuxProfileNeutralSourceProof (lambdaAt exact_OpenNeutralHeaderNotLambda)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Open the literal accepted application and both real scalar inputs.
Its selected result and emitted address are kept in the actual object scopes. -/
theorem exact_OpenLiteralApplicationRows (i : Program 1) (L : Program 3) (x u t : OTerm α)
    (goal : Formula α)
    (accepted : D B Γ (programGraph (applicationGuard i L) (suc z) ![x,u,t]))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β))
      (ctx result dom cod fn arg atResult : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (unary i (suc z) (x.relabel j)) →
      D B Δ (unary i (suc z) (u.relabel j)) →
      D B Δ (parsedApplicationInputs (x.relabel j) (u.relabel j) ctx result dom cod fn arg) →
      D B Δ (programGraph L (suc atResult) ![ctx,cod,auxiliaryTerm dom cod fn arg]) →
      D B Δ (eqn (t.relabel j) (addressTerm ctx cod atResult)) →
      D B Δ (goal.relabel j)) : D B Γ goal := by
  obtain ⟨out⟩ := forward i L x u t accepted
  let tail := Derivation.conjunctionRight out
  have iX : D B Γ (unary i (suc z) x) := ⟨Derivation.conjunctionLeft out⟩
  have iU : D B Γ (unary i (suc z) u) := ⟨Derivation.conjunctionLeft tail⟩
  apply rowCases L x u t goal ⟨Derivation.conjunctionRight tail⟩
  intro β j Δ ctx result dom cod fn arg keep known
  obtain ⟨parsed⟩ := known
  let n : β → β ⊕ Fin 1 := Sum.inl
  let k : OTerm (β ⊕ Fin 1) := .var (.inr 0)
  let row := reportBinder L ctx cod (auxiliaryTerm dom cod fn arg) (t.relabel j)
  let Ω := row :: Δ.map weaken
  have keepN (f : Formula β) (hf : f ∈ Δ) : f.relabel n ∈ Ω :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
  have witnessRow : Derivation B Ω row := Derivation.hypothesis List.mem_cons_self
  have target : D B Ω ((goal.relabel j).relabel n) := by
    let b := n ∘ j
    have keepB (φ : Formula α) (h : φ ∈ Γ) : φ.relabel b ∈ Ω := by
      simpa only [b,formulaRelabelComposition] using keepN _ (keep φ h)
    have p := renameInto (⟨Derivation.conjunctionLeft parsed⟩ :
      D B Δ (parsedApplicationInputs (x.relabel j) (u.relabel j) ctx result dom cod fn arg)) n Ω keepN
    rw [NumberedWindowInternalSparseApplicationFrontendOpenFormulaProof.inputsRename] at p
    have one := renameInto iX b Ω keepB
    have two := renameInto iU b Ω keepB
    simp only [unaryRename,sucRelabel,zRelabel] at one two
    have stored : D B Ω (programGraph L (suc k) ![ctx.relabel n,cod.relabel n,
      (auxiliaryTerm dom cod fn arg).relabel n]) := ⟨Derivation.conjunctionLeft witnessRow⟩
    rw [auxiliaryRename] at stored
    have eq : D B Ω (eqn ((t.relabel j).relabel n) (addressTerm (ctx.relabel n) (cod.relabel n) k)) :=
      ⟨Derivation.conjunctionRight witnessRow⟩
    have returned := use (β ⊕ Fin 1) b Ω (ctx.relabel n) (result.relabel n) (dom.relabel n) (cod.relabel n)
      (fn.relabel n) (arg.relabel n) k keepB one two
      (by simpa only [b,Term.relabel_relabel] using p) stored
      (by simpa only [b,Term.relabel_relabel] using eq)
    simpa only [b,formulaRelabelComposition] using returned
  obtain ⟨body⟩ := target
  have envelope : D B Δ (NumberedWindowInternalSparseApplicationOutputCoreTargets.outputReport L ctx cod
      (auxiliaryTerm dom cod fn arg) (t.relabel j)) := ⟨Derivation.conjunctionRight parsed⟩
  rw [reportUnfold] at envelope
  obtain ⟨witness⟩ := envelope
  exact ⟨Derivation.existentialElimination witness body⟩

#print axioms exact_OpenLiteralApplicationRows
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationRowsProof
