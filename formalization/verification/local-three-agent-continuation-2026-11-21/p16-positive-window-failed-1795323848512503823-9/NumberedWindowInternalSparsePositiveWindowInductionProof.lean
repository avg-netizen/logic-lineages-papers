module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveWindowMotiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveWindowConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressSingletonNilProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityGapProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldInductionChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityGapProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveWindowInductionProof
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
open NumberedWindowInternalSparsePositiveWindowMotiveProof
open NumberedWindowInternalSparsePositiveWindowConsProof (fromCons)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem nilRule (raw : Program 5) (least W : Program 3) (ctx ty target : OTerm α) :
    Nonempty (Derivation body [] (atCode (motive raw least W ctx ty target) z)) := by
  rw [motiveAt]
  apply introduce
  intro β j Δ x _ window good
  rw [zRelabel] at good
  have same := finishNil (body := body) (Γ := Δ) raw least (ctx.relabel j) (ty.relabel j) x
  obtain ⟨eq⟩ := valueUnique (finish raw least) (suc x) (suc (target.relabel j))
    (args4 (ctx.relabel j) (ty.relabel j) (suc x) z) same good
  obtain ⟨g⟩ := window
  exact moveGuard W (ctx.relabel j) (ty.relabel j) x (target.relabel j) (cancelSuc eq) g

private theorem badRule (raw : Program 5) (least W : Program 3) (ctx ty cert target : OTerm α)
    (gap : Nonempty (Derivation body Γ (malformed cert))) :
    Nonempty (Derivation body Γ (safe raw least W ctx ty cert target)) := by
  apply introduce
  intro β j Δ source keep _ finishGood
  have bad := renameInto gap j Δ keep
  rw [gapRename] at bad
  exact badFinish raw least (ctx.relabel j) (ty.relabel j) source (cert.relabel j) (target.relabel j)
    _ bad finishGood

private theorem gapCase (raw : Program 5) (least W : Program 3) (ctx ty target : OTerm α) :
    Nonempty (Derivation body [] (gapRule (motive raw least W ctx ty target))) := by
  let code : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  obtain ⟨r⟩ := badRule (body := body) (Γ := [malformed code]) raw least W (ctx.relabel Sum.inl)
    (ty.relabel Sum.inl) code (target.relabel Sum.inl) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction r)⟩

private theorem consUniform (raw : Program 5) (least W : Program 3) (law : AdvanceWindows raw least W)
    (ctx ty cert h t target : OTerm α) (cell : Nonempty (Derivation body Γ (consGraph cert h t)))
    (hyp : Nonempty (Derivation body Γ (safe raw least W ctx ty t target))) :
    Nonempty (Derivation body Γ (safe raw least W ctx ty cert target)) := by
  apply introduce
  intro β j Δ x keep _ good
  have c := renameInto cell j Δ keep
  rw [consGraphRename] at c
  have ih := renameInto hyp j Δ keep
  rw [safeRename] at ih
  exact fromCons raw least W law (ctx.relabel j) (ty.relabel j) x (cert.relabel j) (target.relabel j)
    (h.relabel j) (t.relabel j) c good ih

private theorem consCase (raw : Program 5) (least W : Program 3) (law : AdvanceWindows raw least W)
    (ctx ty target : OTerm α) : Nonempty (Derivation body [] (consRule (motive raw least W ctx ty target))) := by
  unfold consRule
  apply actualFiniteUniversalIntroduction body α 3 [] (consBody (motive raw least W ctx ty target))
  unfold consBody
  rw [motiveIndex,motiveIndex]
  let code : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let h : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let t : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let cell := consGraph code h t
  let ih := safe raw least W (ctx.relabel Sum.inl) (ty.relabel Sum.inl) t (target.relabel Sum.inl)
  have c : Derivation body [ih,cell] cell := Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨d⟩ := consUniform (Γ := [ih,cell]) raw least W law (ctx.relabel Sum.inl) (ty.relabel Sum.inl)
    code h t (target.relabel Sum.inl) ⟨c⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction d)⟩

theorem finishWindow : ExactFinishWindow := by
  intro raw least W law body α Γ ctx ty source cert target
  obtain ⟨base⟩ := nilRule (body := body) raw least W ctx ty target
  obtain ⟨gap⟩ := gapCase (body := body) raw least W ctx ty target
  obtain ⟨cons⟩ := consCase (body := body) raw least W law ctx ty target
  have all := exact_SparseFieldInductionAtCode body α [] (motive raw least W ctx ty target) cert
    ⟨Derivation.conjunctionIntroduction base (Derivation.conjunctionIntroduction gap cons)⟩
  rw [motiveAt] at all
  obtain ⟨r⟩ := applyAt raw least W ctx ty source cert target all
  exact ⟨weakenClosed r Γ⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveWindowInductionProof
