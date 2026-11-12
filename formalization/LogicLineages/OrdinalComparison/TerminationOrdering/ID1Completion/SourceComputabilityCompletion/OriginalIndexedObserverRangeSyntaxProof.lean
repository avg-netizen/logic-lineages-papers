module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareDichotomySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverRangeSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalFiniteBlocksSubstitutionProof InternalOriginalOrderSyntaxProof InternalQuotientComparisonSyntaxProof
open InternalTagArithmeticSyntaxProof (emb bindEmbedding varBind liftBind)
open OriginalTypedDecoderInternalLogicSyntaxProof OriginalIndexedObserverDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
def rangeFields (cutoff parameter count : OTerm alpha) : Formula alpha :=
  graph1 contextLength count parameter ⊓ OriginalContextInsertion.Below cutoff count

theorem rangeFieldsSubst {beta : Type} (cutoff parameter count : OTerm alpha) (ts : alpha → OTerm beta) :
    (rangeFields cutoff parameter count).subst (fun a => emb (ts a)) =
      rangeFields (cutoff.subst ts) (parameter.subst ts) (count.subst ts) := by
  simp only [rangeFields,conjunctionSubst,graph1,programSubst,consTermSubst,emptySubst,
    OriginalContextInsertion.Below,orderSubst]

theorem rangeSubst {beta : Type} (cutoff parameter : OTerm alpha) (ts : alpha → OTerm beta) :
    (ActualRange cutoff parameter).subst (fun a => emb (ts a)) =
      ActualRange (cutoff.subst ts) (parameter.subst ts) := by
  unfold ActualRange
  rw [existsSubst,liftedEmbedding]
  change (rangeFields (cutoff.relabel Sum.inl) (parameter.relabel Sum.inl) (.var (.inr 0))).subst _ = _
  rw [rangeFieldsSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr] <;> rfl

@[simp] theorem rangeRename {beta : Type} (cutoff parameter : OTerm alpha) (j : alpha → beta) :
    (ActualRange cutoff parameter).relabel j = ActualRange (cutoff.relabel j) (parameter.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (ActualRange cutoff parameter).subst (fun a => emb (.var (j a))) = _
  rw [rangeSubst]
  simp only [← termRelabelAsSubst]

theorem rangeInstantiate (cutoff parameter count : OTerm alpha) :
    instantiate (rangeMatrix cutoff parameter) (emb count) = rangeFields cutoff parameter count := by
  rw [instantiate,bindEmbedding]
  change (rangeFields (cutoff.relabel Sum.inl) (parameter.relabel Sum.inl) (.var (.inr 0))).subst _ = _
  rw [rangeFieldsSubst]
  simp only [varBind,liftBind]

theorem rangeIntro (cutoff parameter count : OTerm alpha)
    (h : Nonempty (Derivation body Delta (rangeFields cutoff parameter count))) :
    Nonempty (Derivation body Delta (ActualRange cutoff parameter)) := by
  obtain ⟨h⟩ := h
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb count)
  rw [rangeInstantiate]
  exact h

theorem rangeCases (cutoff parameter : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Delta (ActualRange cutoff parameter)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (count : OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (rangeFields (cutoff.relabel j) (parameter.relabel j) count)) →
      Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
  obtain ⟨h⟩ := h
  let P := rangeMatrix cutoff parameter
  let Theta := P :: Delta.map weaken
  obtain ⟨d⟩ := next (alpha ⊕ Fin 1) Sum.inl Theta (.var (.inr 0))
    (fun q hq => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.existentialElimination h d⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverRangeSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverRangeSyntaxProof
