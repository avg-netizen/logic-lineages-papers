module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapImageProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding OTerm
open InternalControlGraphSupportProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalFiniteBlocksSubstitutionProof
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable (F : Program 1)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def imageMatrix (raw node : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  graph2 contains (numeral 1) (raw.relabel Sum.inl) (.var (.inr 0)) ⊓
    graph1 F (node.relabel Sum.inl) (.var (.inr 0))
def image (raw node : OTerm alpha) : Formula alpha := existsOne (imageMatrix F raw node)

theorem imageSubst {beta : Type} (raw node : OTerm alpha) (ts : alpha → OTerm beta) :
    (image F raw node).subst (fun a => emb (ts a)) = image F (raw.subst ts) (node.subst ts) := by
  unfold image imageMatrix
  rw [existsSubst,liftedEmbedding]
  simp only [conjunctionSubst,graph1,graph2,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem imageRename {beta : Type} (raw node : OTerm alpha) (j : alpha → beta) :
    (image F raw node).relabel j = image F (raw.relabel j) (node.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (image F raw node).subst (fun a => emb (.var (j a))) = _
  rw [imageSubst]
  simp only [← termRelabelAsSubst]

theorem imageWitness (raw node source : OTerm alpha) :
    InternalCalculus.instantiate (imageMatrix F raw node) (emb source) =
      (graph2 contains (numeral 1) raw source ⊓ graph1 F node source) := by
  unfold imageMatrix InternalCalculus.instantiate
  rw [bindEmbedding]
  simp only [conjunctionSubst,graph1,graph2,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]

theorem introduce (raw node source : OTerm alpha)
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw source)))
    (hv : Nonempty (Derivation body Delta (graph1 F node source))) :
    Nonempty (Derivation body Delta (image F raw node)) := by
  obtain ⟨hm⟩ := hm
  obtain ⟨hv⟩ := hv
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb source)
  rw [imageWitness]
  exact Derivation.conjunctionIntroduction hm hv
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapImageProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapImageProof
