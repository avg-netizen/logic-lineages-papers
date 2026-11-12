module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareDichotomyDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalVariableSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareDichotomySyntaxProof
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
open OriginalLambdaErasureSquareDichotomyDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem fieldsSubst {beta : Type} (leaf : Program 4) (s t parameter cert : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (Certificate leaf s t parameter cert).subst (fun a => emb (ts a)) =
      Certificate leaf (s.subst ts) (t.subst ts) (parameter.subst ts) (cert.subst ts) := by
  simp only [Certificate,graph1,graph4,programSubst,consTermSubst,emptySubst,
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
    instantiate (WitnessMatrix leaf s t parameter) (emb cert) = Certificate leaf s t parameter cert := by
  rw [instantiate,bindEmbedding]
  unfold WitnessMatrix
  rw [fieldsSubst]
  simp only [varBind,liftBind]

theorem witnessIntro (leaf : Program 4) (s t parameter cert : OTerm alpha)
    (h : Nonempty (Derivation body Delta (Certificate leaf s t parameter cert))) :
    Nonempty (Derivation body Delta (Witness leaf s t parameter)) := by
  obtain ⟨h⟩ := h
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb cert)
  rw [witnessInstantiate]
  exact h
@[simp] theorem frameRename {beta : Type} (source : Program 2)
    (s t parameter childS childT childParam d e context gamma extended : OTerm alpha)
    (j : alpha → beta) :
    (Frame source s t parameter childS childT childParam d e context gamma extended).relabel j =
      Frame source (s.relabel j) (t.relabel j) (parameter.relabel j) (childS.relabel j) (childT.relabel j)
        (childParam.relabel j) (d.relabel j) (e.relabel j) (context.relabel j) (gamma.relabel j) (extended.relabel j) := by
  simp only [Frame,conjunctionRename,graph1Rename,graph2Rename,graph3Rename,
    InternalOriginalStepGuard.one,InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel]

@[simp] theorem resultRename {beta : Type} (leaf : Program 4) (s t parameter : OTerm alpha) (j : alpha → beta) :
    (Result leaf s t parameter).relabel j = Result leaf (s.relabel j) (t.relabel j) (parameter.relabel j) := by
  simp only [Result,disjunctionRename,equalRename,witnessRename]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareDichotomySyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareDichotomySyntaxProof
