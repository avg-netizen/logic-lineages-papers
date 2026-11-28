module
public import LogicLineages.PersistentMarking.NumberedWindowComputabilityFormulaTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaOperandAlignmentProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterObjectTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicAddressReportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaAcceptedChildProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictImageRetapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowTypeApplicationRuleChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAlignedBetaTargetProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.OrdinalComparison.Source (Ty)
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel emb bindEmbedding varBind)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc refl symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowComputabilityFormulaTargets (formula)
open NumberedWindowTypeApplicationRuleChecks (exact_FormulaSubstitution)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename tripleInputsRename)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseAddressPositiveOpenBindingProof (addressReportRename)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralBetaOperandAlignmentProof (AlignedBetaRow)
open NumberedWindowInternalLiteralAtomicAddressReportProof (rebuildAddress)
open NumberedWindowInternalLiteralSingletonLambdaAcceptedChildProof (rawLambdaTermRename)
open NumberedWindowInternalLiteralStrictImageRetapeProof (exact_OpenStrictRetapeTypeAndRaw)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Carry the open row into the context introduced by decoding an object
language witness, keeping all of its programs and coordinates. -/
theorem exact_OpenAlignedBetaRowRename {L₀ L : Program 3} {U : Program 2}
    {ctx dom cod fn arg sc st after q r d e f a bind body y : OTerm α}
    (row : AlignedBetaRow L₀ L U B Γ ctx dom cod fn arg sc st after q r d e f a bind body y)
    {β : Type} (j : α → β) (Δ : List (Formula β)) (keep : ∀ p ∈ Γ, p.relabel j ∈ Δ) :
    AlignedBetaRow L₀ L U B Δ (ctx.relabel j) (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)
      (sc.relabel j) (st.relabel j) (after.relabel j) (q.relabel j) (r.relabel j) (d.relabel j) (e.relabel j)
      (f.relabel j) (a.relabel j) (bind.relabel j) (body.relabel j) (y.relabel j) where
  source := by simpa only [eqnRelabel,auxiliaryRename] using renameInto row.source j Δ keep
  functionShape := by simpa only [eqnRelabel,rawLambdaTermRename] using renameInto row.functionShape j Δ keep
  binderType := by simpa only [eqnRelabel] using renameInto row.binderType j Δ keep
  domain := by simpa only [eqnRelabel] using renameInto row.domain j Δ keep
  codomain := by simpa only [eqnRelabel] using renameInto row.codomain j Δ keep
  functionClass := by
    simpa only [programRename,tripleInputsRename,sucRelabel,rawConsRename] using renameInto row.functionClass j Δ keep
  argumentClass := by
    simpa only [programRename,tripleInputsRename,sucRelabel] using renameInto row.argumentClass j Δ keep
  instanceRun := by
    simpa only [programRename,binaryInputsRename,sucRelabel] using renameInto row.instanceRun j Δ keep
  targetClass := by
    simpa only [programRename,tripleInputsRename,sucRelabel] using renameInto row.targetClass j Δ keep
  targetAddress := by simpa only [addressReportRename] using renameInto row.targetAddress j Δ keep

/-- The open instance equation identifies the raw beta target. The actual
least report at this code and the actual addressed reduct retain the
same context, type and least code from the aligned row. -/
theorem exact_OpenAlignedBetaTarget {L₀ L : Program 3} {U : Program 2}
    {ctx dom cod fn arg sc st after q r d e f a bind body y : OTerm α} (rebuilt : OTerm α)
    (row : AlignedBetaRow L₀ L U B Γ ctx dom cod fn arg sc st after q r d e f a bind body y)
    (output : D B Γ (eqn (suc r) (suc rebuilt))) :
    D B Γ (eqn r rebuilt) ∧
    D B Γ (programGraph L (suc after) ![sc,st,rebuilt]) ∧
    D B Γ (eqn y (addressTerm sc st after)) := by
  obtain ⟨found⟩ := output
  have same : D B Γ (eqn r rebuilt) := ⟨cancelSuc found⟩
  exact ⟨same,
    exact_OpenStrictRetapeTypeAndRaw L sc st st r rebuilt (suc after) ⟨refl st⟩ same row.targetClass,
    rebuildAddress y sc st after sc st after row.targetAddress ⟨refl sc⟩ ⟨refl st⟩ ⟨refl after⟩⟩

/-- Use computability of the rebuilt instance at its checked least
address to obtain computability of the very reduct in the beta row. -/
theorem exact_OpenComputabilityOfAlignedBetaTarget {L₀ L : Program 3} {U : Program 2}
    {ctx dom cod fn arg sc st after q r d e f a bind body y : OTerm α}
    (p : Program 3) (τ : Ty) (rebuilt : OTerm α)
    (row : AlignedBetaRow L₀ L U B Γ ctx dom cod fn arg sc st after q r d e f a bind body y)
    (output : D B Γ (eqn (suc r) (suc rebuilt)))
    (use : D B Γ (programGraph L (suc after) ![sc,st,rebuilt]) →
      D B Γ (formula p τ (addressTerm sc st after))) : D B Γ (formula p τ y) := by
  obtain ⟨_,least,⟨address⟩⟩ := exact_OpenAlignedBetaTarget rebuilt row output
  obtain ⟨computed⟩ := use least
  let θ : Formula (α ⊕ Fin 1) := formula p τ (.var (.inr 0))
  have atTerm (x : OTerm α) : instantiate θ (emb x) = formula p τ x := by
    change instantiate (formula p τ (.var (.inr 0))) (emb x) = formula p τ x
    rw [instantiate,bindEmbedding,exact_FormulaSubstitution p τ (α ⊕ Fin 1) α _,varBind]
  have moved := Derivation.equalityElimination θ (emb (addressTerm sc st after)) (emb y)
    (symm address) (by rw [atTerm]; exact computed)
  rw [atTerm] at moved
  exact ⟨moved⟩

#print axioms exact_OpenAlignedBetaRowRename
#print axioms exact_OpenAlignedBetaTarget
#print axioms exact_OpenComputabilityOfAlignedBetaTarget
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAlignedBetaTargetProof
