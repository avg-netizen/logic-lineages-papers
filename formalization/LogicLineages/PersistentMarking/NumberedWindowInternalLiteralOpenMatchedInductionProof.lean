module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOpenMatchedMotiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOpenMatchedConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressSingletonNilProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityGapProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldInductionChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityGapProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof

import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenFormulaProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastSubstitutionThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOpenMatchedInductionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveOutputTargets (args4)
open NumberedWindowInternalSparsePositiveFold (finish)
open NumberedWindowInternalSparseFieldInductionTargets
open NumberedWindowInternalSparseFieldExistentialProof (consGraphRename)
open NumberedWindowInternalSparsePositiveTerminalityGapProof (gapRename)
open NumberedWindowInternalSparseFieldInductionChecks (exact_SparseFieldInductionAtCode)
open NumberedWindowInternalSparsePassWindowSyntaxProof (moveGuard)
open NumberedWindowInternalSparseAddressSingletonNilProof (finishNil)
open NumberedWindowInternalSparsePositiveTransitivityGapProof (badFinish)
open NumberedWindowInternalSparsePositiveWindowTargets
open NumberedWindowInternalLiteralOpenMatchedMotiveProof
open NumberedWindowInternalLiteralOpenMatchedConsProof (fromCons)

open NumberedWindowInternalLiteralOpenMatchedReportProof
open NumberedWindowInternalLiteralOpenMatchedAdvanceLawProof (MatchedAdvanceAt resultOrPath)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationFrontendOpenFormulaProof (auxiliarySubst)
open NumberedWindowInternalLiteralOpenMatchedPathLawProof
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind eqn)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
attribute [local irreducible] ID1Completion.InternalControlGraph.programGraph
variable (K : MatchContext) (L : Program 3) (raw : Program 5)
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}


private theorem moveFunction (ctx dom cod arg a b value : OTerm α) (same : Derivation body Γ (eqn a b))
    (d : Derivation body Γ (reported L ctx cod (auxiliaryTerm dom cod a arg) value)) :
    Nonempty (Derivation body Γ (reported L ctx cod (auxiliaryTerm dom cod b arg) value)) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let clause := reported L (ctx.relabel j) (cod.relabel j)
    (auxiliaryTerm (dom.relabel j) (cod.relabel j) (.var (.inr 0)) (arg.relabel j)) (value.relabel j)
  have inst (t : OTerm α) : instantiate clause (emb t) = reported L ctx cod (auxiliaryTerm dom cod t arg) value := by
    simp only [clause,j,instantiate,bindEmbedding,reportedSubst,auxiliarySubst,liftBind,varBind]
  exact ⟨(inst b) ▸ Derivation.equalityElimination clause (emb a) (emb b) same ((inst a).symm ▸ d)⟩

private theorem nilRule (ctx dom cod arg target value : OTerm α) :
    Nonempty (Derivation body [] (atCode (motive K L raw ctx dom cod arg target value) z)) := by
  rw [motiveAt]
  apply introduce
  intro β j Δ x _ _ checked observed
  rw [zRelabel] at checked
  let least := L
  let ty := (rawCons dom cod).relabel j
  have literal := finishNil (body := body) (Γ := Δ) raw least (ctx.relabel j) ty x
  obtain ⟨same⟩ := valueUnique (finish raw least) (suc x) (suc (target.relabel j))
    (args4 (ctx.relabel j) ty (suc x) z) literal ⟨checked⟩
  obtain ⟨atX⟩ := moveFunction L _ _ _ _ (target.relabel j) x _ (symm (cancelSuc same)) observed
  exact ⟨orLeft atX⟩

private theorem badRule (ctx dom cod arg cert target value : OTerm α)
    (gap : Nonempty (Derivation body Γ (malformed cert))) :
    Nonempty (Derivation body Γ (safe K L raw ctx dom cod arg cert target value)) := by
  apply introduce
  intro β j Δ x keep _ good _
  have bad := renameInto gap j Δ keep
  rw [gapRename] at bad
  exact badFinish raw (L) _ _ x _ _ _ bad ⟨good⟩

private theorem gapCase (ctx dom cod arg target value : OTerm α) :
    Nonempty (Derivation body [] (gapRule (motive K L raw ctx dom cod arg target value))) := by
  let code : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  obtain ⟨r⟩ := badRule (body := body) (Γ := [malformed code]) K L raw (ctx.relabel Sum.inl)
    (dom.relabel Sum.inl) (cod.relabel Sum.inl) (arg.relabel Sum.inl) code (target.relabel Sum.inl)
    (value.relabel Sum.inl) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction r)⟩

private theorem consUniform (law : MatchedAdvanceAt K L raw) (ctx dom cod arg cert target value hd tl : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph cert hd tl)))
    (hyp : Nonempty (Derivation body Γ (safe K L raw ctx dom cod arg tl target value))) :
    Nonempty (Derivation body Γ (safe K L raw ctx dom cod arg cert target value)) := by
  apply introduce
  intro β j Δ x keep form done last
  have c := renameInto cell j Δ keep
  rw [consGraphRename] at c
  have old := renameInto hyp j Δ keep
  rw [safeRename] at old
  rw [rawConsRename] at done
  obtain ⟨path⟩ := fromCons K L raw law (ctx.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j)
    x (cert.relabel j) (target.relabel j) (value.relabel j) (hd.relabel j) (tl.relabel j) c form done last old
  exact ⟨orRight path⟩

private theorem consCase (law : MatchedAdvanceAt K L raw) (ctx dom cod arg target value : OTerm α) :
    Nonempty (Derivation body [] (consRule (motive K L raw ctx dom cod arg target value))) := by
  unfold consRule
  apply actualFiniteUniversalIntroduction body α 3 [] (consBody (motive K L raw ctx dom cod arg target value))
  unfold consBody
  rw [motiveIndex,motiveIndex]
  let j : α → α ⊕ Fin 3 := Sum.inl
  let code : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let hd : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let tl : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let cell := consGraph code hd tl
  let ih := safe K L raw (ctx.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j) tl
    (target.relabel j) (value.relabel j)
  have c : Derivation body [ih,cell] cell := Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨d⟩ := consUniform K L raw law (ctx.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j)
    code (target.relabel j) (value.relabel j) hd tl ⟨c⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction d)⟩

theorem finishMatching : ExactMatchedFinish := by
  intro K L raw law body α Γ ctx dom cod arg fn next cert value
  obtain ⟨base⟩ := nilRule (body := body) K L raw ctx dom cod arg next value
  obtain ⟨gap⟩ := gapCase (body := body) K L raw ctx dom cod arg next value
  obtain ⟨cons⟩ := consCase (body := body) K L raw law ctx dom cod arg next value
  have all := exact_SparseFieldInductionAtCode body α [] (motive K L raw ctx dom cod arg next value) cert
    ⟨Derivation.conjunctionIntroduction base (Derivation.conjunctionIntroduction gap cons)⟩
  rw [motiveAt] at all
  obtain ⟨all⟩ := all
  obtain ⟨d⟩ := applyAt K L raw ctx dom cod arg cert next value fn all
  exact ⟨weakenClosed d Γ⟩

#print axioms finishMatching
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOpenMatchedInductionProof
