module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.GuardedErasureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareDichotomySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.GuardedErasureSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalRawListRecursionSyntaxProof (programSubst consTermSubst emptySubst)
open InternalGraphCompositionSyntaxProof InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalFiniteBlocksSubstitutionProof
open InternalTagArithmeticSyntaxProof (emb bindEmbedding varBind liftBind sucSubst zSubst)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open GuardedErasureTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem certificateSubst {beta : Type} (D : InternalOriginalUniformDescentSelection.Data)
    (oldStep rawLeaf : Program 4) (s t cert parameter : OTerm alpha) (ts : alpha → OTerm beta) :
    (Certificate D oldStep rawLeaf s t cert parameter).subst (fun a => emb (ts a)) =
      Certificate D oldStep rawLeaf (s.subst ts) (t.subst ts) (cert.subst ts) (parameter.subst ts) := by
  simp only [Certificate,UniformCertificateCompletion.stepAccepted,graph4,programSubst,
    consTermSubst,emptySubst,conjunctionSubst,numeral,InternalOriginalStepGuard.one,sucSubst,zSubst]

theorem witnessSubst {beta : Type} (D : InternalOriginalUniformDescentSelection.Data)
    (oldStep rawLeaf : Program 4) (s t parameter : OTerm alpha) (ts : alpha → OTerm beta) :
    (Witness D oldStep rawLeaf s t parameter).subst (fun a => emb (ts a)) =
      Witness D oldStep rawLeaf (s.subst ts) (t.subst ts) (parameter.subst ts) := by
  unfold Witness
  rw [existsSubst,liftedEmbedding]
  unfold WitnessMatrix
  simp only [certificateSubst,liftSubst,Term.subst,Sum.elim_inr] <;> rfl

theorem certificateRename {beta : Type} (D : InternalOriginalUniformDescentSelection.Data)
    (oldStep rawLeaf : Program 4) (s t cert parameter : OTerm alpha) (j : alpha → beta) :
    (Certificate D oldStep rawLeaf s t cert parameter).relabel j =
      Certificate D oldStep rawLeaf (s.relabel j) (t.relabel j) (cert.relabel j) (parameter.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (Certificate D oldStep rawLeaf s t cert parameter).subst (fun a => emb (.var (j a))) = _
  rw [certificateSubst]
  simp only [← termRelabelAsSubst]

theorem witnessRename {beta : Type} (D : InternalOriginalUniformDescentSelection.Data)
    (oldStep rawLeaf : Program 4) (s t parameter : OTerm alpha) (j : alpha → beta) :
    (Witness D oldStep rawLeaf s t parameter).relabel j =
      Witness D oldStep rawLeaf (s.relabel j) (t.relabel j) (parameter.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (Witness D oldStep rawLeaf s t parameter).subst (fun a => emb (.var (j a))) = _
  rw [witnessSubst]
  simp only [← termRelabelAsSubst]

theorem witnessInstantiate (D : InternalOriginalUniformDescentSelection.Data)
    (oldStep rawLeaf : Program 4) (s t cert parameter : OTerm alpha) :
    instantiate (WitnessMatrix D oldStep rawLeaf s t parameter) (emb cert) =
      Certificate D oldStep rawLeaf s t cert parameter := by
  rw [instantiate,bindEmbedding]
  unfold WitnessMatrix
  rw [certificateSubst]
  simp only [varBind,liftBind]

theorem witnessIntro (D : InternalOriginalUniformDescentSelection.Data)
    (oldStep rawLeaf : Program 4) (s t cert parameter : OTerm alpha)
    (h : Nonempty (Derivation body Delta (Certificate D oldStep rawLeaf s t cert parameter))) :
    Nonempty (Derivation body Delta (Witness D oldStep rawLeaf s t parameter)) := by
  obtain ⟨h⟩ := h
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb cert)
  rw [witnessInstantiate]
  exact h

theorem resultRename {beta : Type} (D : InternalOriginalUniformDescentSelection.Data)
    (oldStep rawLeaf : Program 4) (s t parameter oldS oldT : OTerm alpha) (j : alpha → beta) :
    (Result D oldStep rawLeaf s t parameter oldS oldT).relabel j =
      Result D oldStep rawLeaf (s.relabel j) (t.relabel j) (parameter.relabel j)
        (oldS.relabel j) (oldT.relabel j) := by
  simp only [Result,OriginalLambdaErasureSquareDichotomySyntaxProof.localOrRename,
    conjunctionRename,equalRename,OriginalExistentialRankResultSyntaxProof.rankWitnessRename,witnessRename]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.GuardedErasureSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.GuardedErasureSyntaxProof
