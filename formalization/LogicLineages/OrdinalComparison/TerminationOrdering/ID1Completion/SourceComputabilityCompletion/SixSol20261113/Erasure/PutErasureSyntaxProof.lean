module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutErasureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareDichotomySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutErasureSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalRawListRecursionSyntaxProof (programSubst consTermSubst emptySubst)
open InternalGraphCompositionSyntaxProof InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalFiniteBlocksSubstitutionProof
open InternalTagArithmeticSyntaxProof (emb bindEmbedding varBind liftBind sucSubst zSubst)
open SourceComputabilityFormulaSupportProof (numeral existsOne)
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open UniformCertificateCompletion PutErasure
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}


def Certificate {alpha : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (s t parameter label cert : OTerm alpha) : Formula alpha :=
  graph2 SixSol20261112.Erasure.PutRoot.certificateCode cert s label ⊓
    stepAccepted (PutIntegration.finalData p H G W P) (PutIntegration.finalInputs p H G W P).oldStep s t cert parameter

theorem certificateSubst {beta : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (s t parameter label cert : OTerm alpha) (ts : alpha → OTerm beta) :
    (Certificate p H G W P s t parameter label cert).subst (fun a => emb (ts a)) =
      Certificate p H G W P (s.subst ts) (t.subst ts) (parameter.subst ts) (label.subst ts) (cert.subst ts) := by
  simp only [Certificate,stepAccepted,graph2,graph4,programSubst,consTermSubst,emptySubst,
    conjunctionSubst,InternalOriginalStepGuard.one,sucSubst,zSubst]

theorem witnessSubst {beta : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (s t parameter label : OTerm alpha) (ts : alpha → OTerm beta) :
    (Witness p H G W P s t parameter label).subst (fun a => emb (ts a)) =
      Witness p H G W P (s.subst ts) (t.subst ts) (parameter.subst ts) (label.subst ts) := by
  unfold Witness
  rw [existsSubst,liftedEmbedding]
  apply congrArg existsOne
  change (Certificate p H G W P _ _ _ _ _).subst _ = _
  simp only [certificateSubst,liftSubst,Term.subst,Sum.elim_inr] <;> rfl

theorem witnessRename {beta : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (s t parameter label : OTerm alpha) (j : alpha → beta) :
    (Witness p H G W P s t parameter label).relabel j =
      Witness p H G W P (s.relabel j) (t.relabel j) (parameter.relabel j) (label.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (Witness p H G W P s t parameter label).subst (fun a => emb (.var (j a))) = _
  rw [witnessSubst]
  simp only [← termRelabelAsSubst]

theorem witnessInstantiate (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (s t parameter label cert : OTerm alpha) :
    instantiate (WitnessMatrix p H G W P s t parameter label) (emb cert) =
      Certificate p H G W P s t parameter label cert := by
  rw [instantiate,bindEmbedding]
  change (Certificate p H G W P _ _ _ _ _).subst _ = _
  rw [certificateSubst]
  simp only [varBind,liftBind]

theorem witnessIntro (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (s t parameter label cert : OTerm alpha)
    (h : Nonempty (Derivation body Delta (Certificate p H G W P s t parameter label cert))) :
    Nonempty (Derivation body Delta (Witness p H G W P s t parameter label)) := by
  obtain ⟨h⟩ := h
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb cert)
  rw [witnessInstantiate]
  exact h
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutErasureSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutErasureSyntaxProof
