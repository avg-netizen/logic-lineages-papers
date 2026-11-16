module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.PairImageProof
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
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def imageMatrix (raw param node : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  graph2 contains (numeral 1) (raw.relabel Sum.inl) (.var (.inr 0)) ⊓
    graph2 InternalPairing.pairing (node.relabel Sum.inl) (param.relabel Sum.inl) (.var (.inr 0))
def image (raw param node : OTerm alpha) : Formula alpha := existsOne (imageMatrix raw param node)

theorem imageSubst {beta : Type} (raw param node : OTerm alpha) (ts : alpha → OTerm beta) :
    (image raw param node).subst (fun a => emb (ts a)) = image (raw.subst ts) (param.subst ts) (node.subst ts) := by
  unfold image imageMatrix
  rw [existsSubst,liftedEmbedding]
  simp only [conjunctionSubst,graph1,graph2,InternalComputabilityApplicationSyntaxProof.programSubst,numeral,zSubst,sucSubst,
    InternalRawListRecursionSyntaxProof.consTermSubst,InternalRawListRecursionSyntaxProof.emptySubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem imageRename {beta : Type} (raw param node : OTerm alpha) (j : alpha → beta) :
    (image raw param node).relabel j = image (raw.relabel j) (param.relabel j) (node.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (image raw param node).subst (fun a => emb (.var (j a))) = _
  rw [imageSubst]
  simp only [← termRelabelAsSubst]

theorem imageWitness (raw param node source : OTerm alpha) :
    InternalCalculus.instantiate (imageMatrix raw param node) (emb source) =
      (graph2 contains (numeral 1) raw source ⊓ graph2 InternalPairing.pairing node param source) := by
  unfold imageMatrix InternalCalculus.instantiate
  rw [bindEmbedding]
  simp only [conjunctionSubst,graph1,graph2,InternalComputabilityApplicationSyntaxProof.programSubst,numeral,zSubst,sucSubst,
    InternalRawListRecursionSyntaxProof.consTermSubst,InternalRawListRecursionSyntaxProof.emptySubst,InternalTagArithmeticSyntaxProof.liftBind,InternalTagArithmeticSyntaxProof.varBind]

theorem introduce (raw param node source : OTerm alpha)
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw source)))
    (hv : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node param source))) :
    Nonempty (Derivation body Delta (image raw param node)) := by
  obtain ⟨hm⟩ := hm
  obtain ⟨hv⟩ := hv
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb source)
  rw [imageWitness]
  exact Derivation.conjunctionIntroduction hm hv
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.PairImageProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.PairImageProof
