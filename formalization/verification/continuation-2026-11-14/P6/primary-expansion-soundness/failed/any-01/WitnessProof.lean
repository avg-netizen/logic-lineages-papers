module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.FilterStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.AnyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.WitnessProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSupportProof InternalAcceptanceSupportProof
open InternalApplicationStepPeelSupportProof (andIntro)
open TwoSol20261113.CalibratedPrimary.Membership
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

@[simp] theorem witnessSubst (E : Program 3) {alpha beta : Type}
    (reached candidate parameter : OrdinaryArithmetic.Term alpha) (ts : alpha → OrdinaryArithmetic.Term beta) :
    (sourceWitness E reached candidate parameter).subst (fun a => emb (ts a)) =
      sourceWitness E (reached.subst ts) (candidate.subst ts) (parameter.subst ts) := by
  unfold sourceWitness
  rw [existsSubst,liftedEmbedding,conjunctionSubst]
  simp only [graph2,graph3,programSubst,numeral,zSubst,sucSubst,consTermSubst,emptySubst,
    liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem witnessRename (E : Program 3) {alpha beta : Type}
    (reached candidate parameter : OrdinaryArithmetic.Term alpha) (j : alpha → beta) :
    (sourceWitness E reached candidate parameter).relabel j =
      sourceWitness E (reached.relabel j) (candidate.relabel j) (parameter.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (sourceWitness E reached candidate parameter).subst (fun a => emb (.var (j a))) = _
  rw [witnessSubst]
  simp only [← termRelabelAsSubst]

theorem witnessInstance (E : Program 3) {alpha : Type}
    (reached candidate parameter source : OrdinaryArithmetic.Term alpha) :
    instantiate (graph2 contains (numeral 1) (reached.relabel Sum.inl) (.var (.inr 0)) ⊓
      graph3 E (numeral 1) (.var (.inr 0)) (candidate.relabel Sum.inl) (parameter.relabel Sum.inl))
        (emb source) =
      (graph2 contains (numeral 1) reached source ⊓ graph3 E (numeral 1) source candidate parameter) := by
  rw [instantiate,bindEmbedding,conjunctionSubst]
  simp only [graph2,graph3,programSubst,numeral,zSubst,sucSubst,consTermSubst,emptySubst,liftBind,varBind]

theorem introduction (E : Program 3) {body : Positive (Fin 1)} {alpha : Type}
    {Delta : List (Formula alpha)} (reached candidate parameter source : OrdinaryArithmetic.Term alpha)
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) reached source)))
    (he : Nonempty (Derivation body Delta (graph3 E (numeral 1) source candidate parameter))) :
    Nonempty (Derivation body Delta (sourceWitness E reached candidate parameter)) := by
  obtain ⟨hm⟩ := hm
  obtain ⟨he⟩ := he
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb source)
  rw [witnessInstance]
  exact Derivation.conjunctionIntroduction hm he

theorem casesWitness (E : Program 3) {body : Positive (Fin 1)} {alpha : Type}
    {Delta : List (Formula alpha)} (reached candidate parameter : OrdinaryArithmetic.Term alpha) (goal : Formula alpha)
    (h : Nonempty (Derivation body Delta (sourceWitness E reached candidate parameter)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (source : OrdinaryArithmetic.Term beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 contains (numeral 1) (reached.relabel j) source)) →
      Nonempty (Derivation body Theta (graph3 E (numeral 1) source (candidate.relabel j) (parameter.relabel j))) →
      Nonempty (Derivation body Theta (goal.relabel j))) :
    Nonempty (Derivation body Delta goal) := by
  obtain ⟨h⟩ := h
  let A : Formula (alpha ⊕ Fin 1) :=
    graph2 contains (numeral 1) (reached.relabel Sum.inl) (.var (.inr 0)) ⊓
      graph3 E (numeral 1) (.var (.inr 0)) (candidate.relabel Sum.inl) (parameter.relabel Sum.inl)
  obtain ⟨d⟩ := next (alpha ⊕ Fin 1) Sum.inl (A :: Delta.map weaken) (.var (.inr 0))
    (fun q hq => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  exact ⟨Derivation.existentialElimination h d⟩

theorem prepend (E : Program 3) {body : Positive (Fin 1)} {alpha : Type}
    {Delta : List (Formula alpha)} (raw head tail candidate parameter : OrdinaryArithmetic.Term alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hw : Nonempty (Derivation body Delta (sourceWitness E tail candidate parameter))) :
    Nonempty (Derivation body Delta (sourceWitness E raw candidate parameter)) := by
  apply casesWitness E tail candidate parameter _ hw
  intro beta j Theta source hj hm he
  rw [witnessRename]
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hc'
  exact introduction E (raw.relabel j) (candidate.relabel j) (parameter.relabel j) source
    (PrimaryEdgeInclusion.FilterStepProof.consContainsTail (raw.relabel j) (head.relabel j)
      (tail.relabel j) source hc' hm) he
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.WitnessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.WitnessProof
