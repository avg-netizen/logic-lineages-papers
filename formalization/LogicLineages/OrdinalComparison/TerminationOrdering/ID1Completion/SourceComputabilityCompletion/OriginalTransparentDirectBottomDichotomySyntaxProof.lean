module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomDichotomyTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalVariableSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomDichotomySyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalFiniteBlocksSubstitutionProof
open InternalTagArithmeticSyntaxProof (emb bindEmbedding varBind liftBind)
open OriginalTypedDecoderInternalLogicSyntaxProof
open OriginalTransparentDirectBottomDichotomy
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem fieldsSubst {beta : Type} (leaf : Program 4) (s t parameter cert : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (WitnessFields leaf s t parameter cert).subst (fun a => emb (ts a)) =
      WitnessFields leaf (s.subst ts) (t.subst ts) (parameter.subst ts) (cert.subst ts) := by
  simp only [WitnessFields,graph1,graph4,programSubst,consTermSubst,emptySubst,
    conjunctionSubst,InternalOriginalStepGuard.one,InternalTagArithmeticSyntaxProof.sucSubst,
    InternalTagArithmeticSyntaxProof.zSubst]

theorem witnessSubst {beta : Type} (leaf : Program 4) (s t parameter : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (Witness leaf s t parameter).subst (fun a => emb (ts a)) =
      Witness leaf (s.subst ts) (t.subst ts) (parameter.subst ts) := by
  unfold Witness
  rw [existsSubst,liftedEmbedding]
  unfold WitnessMatrix
  simp only [fieldsSubst,liftSubst,Term.subst,Sum.elim_inr] <;> rfl

@[simp] theorem witnessRename {beta : Type} (leaf : Program 4) (s t parameter : OTerm alpha)
    (j : alpha → beta) :
    (Witness leaf s t parameter).relabel j = Witness leaf (s.relabel j) (t.relabel j) (parameter.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (Witness leaf s t parameter).subst (fun a => emb (.var (j a))) = _
  rw [witnessSubst]
  simp only [← termRelabelAsSubst]

theorem witnessInstantiate (leaf : Program 4) (s t parameter cert : OTerm alpha) :
    instantiate (WitnessMatrix leaf s t parameter) (emb cert) = WitnessFields leaf s t parameter cert := by
  rw [instantiate,bindEmbedding]
  unfold WitnessMatrix
  rw [fieldsSubst]
  simp only [varBind,liftBind]

theorem witnessIntro (leaf : Program 4) (s t parameter cert : OTerm alpha)
    (h : Nonempty (Derivation body Delta (WitnessFields leaf s t parameter cert))) :
    Nonempty (Derivation body Delta (Witness leaf s t parameter)) := by
  obtain ⟨h⟩ := h
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb cert)
  rw [witnessInstantiate]
  exact h
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomDichotomySyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomDichotomySyntaxProof
