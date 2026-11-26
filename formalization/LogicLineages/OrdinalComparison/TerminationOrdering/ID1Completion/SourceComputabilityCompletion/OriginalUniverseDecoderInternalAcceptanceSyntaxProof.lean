module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelSingletonProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (emb eqnSubst sucSubst zSubst sucRelabel zRelabel)
open InternalGraphCompositionSyntaxProof InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalRawListRecursionSyntaxProof OriginalLambdaConstructorGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoderStepSpecification OriginalUniverseDecoderInternalFuel OriginalUniverseDecoderInternalAcceptance
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalUniverseDecoderInternalFuelIterationSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem quadrupleSubst {alpha beta : Type} (a b c d : OTerm alpha) (ts : alpha → OTerm beta) :
    (fun i : Fin 4 => (![a,b,c,d] i).subst ts) = ![a.subst ts,b.subst ts,c.subst ts,d.subst ts] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) i

theorem termAcceptedSubst {alpha beta : Type} (H : Program 1) (M W : Program 2) (typ raw gamma c : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (TermAccepted H M W typ raw gamma c).subst (fun a => emb (ts a)) =
      TermAccepted H M W (typ.subst ts) (raw.subst ts) (gamma.subst ts) (c.subst ts) := by
  simp only [TermAccepted,programSubst,quadrupleSubst,numeral,sucSubst,zSubst]

@[simp] theorem termAcceptedRename {alpha beta : Type} (H : Program 1) (M W : Program 2)
    (typ raw gamma c : OTerm alpha) (j : alpha → beta) :
    (TermAccepted H M W typ raw gamma c).relabel j =
      TermAccepted H M W (typ.relabel j) (raw.relabel j) (gamma.relabel j) (c.relabel j) := by
  simp only [TermAccepted,programRename,oneRename,OriginalUniverseDecoderInternalFuelSingletonProof.quadrupleRename]

theorem argumentsAcceptedSubst {alpha beta : Type} (H : Program 1) (M W : Program 2) (types raw gamma c : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (ArgumentsAccepted H M W types raw gamma c).subst (fun a => emb (ts a)) =
      ArgumentsAccepted H M W (types.subst ts) (raw.subst ts) (gamma.subst ts) (c.subst ts) := by
  simp only [ArgumentsAccepted,programSubst,quadrupleSubst,numeral,sucSubst,zSubst]

@[simp] theorem argumentsAcceptedRename {alpha beta : Type} (H : Program 1) (M W : Program 2)
    (types raw gamma c : OTerm alpha) (j : alpha → beta) :
    (ArgumentsAccepted H M W types raw gamma c).relabel j =
      ArgumentsAccepted H M W (types.relabel j) (raw.relabel j) (gamma.relabel j) (c.relabel j) := by
  simp only [ArgumentsAccepted,programRename,oneRename,OriginalUniverseDecoderInternalFuelSingletonProof.quadrupleRename]

def stateFields {alpha : Type} (H : Program 1) (M W : Program 2) (state work c : OTerm alpha) : Formula alpha :=
  StepLive state work ⊓ WorkAccepted H M W work c

def stateMatrix {alpha : Type} (H : Program 1) (M W : Program 2) (state c : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  stateFields H M W (state.relabel Sum.inl) (.var (.inr 0)) (c.relabel Sum.inl)

theorem stateFieldsSubst {alpha beta : Type} (H : Program 1) (M W : Program 2) (state work c : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (stateFields H M W state work c).subst (fun a => emb (ts a)) =
      stateFields H M W (state.subst ts) (work.subst ts) (c.subst ts) := by
  simp only [stateFields,conjunctionSubst,stepLiveSubst,workAcceptedSubst]

theorem stateMatrixWitness {alpha : Type} (H : Program 1) (M W : Program 2) (state work c : OTerm alpha) :
    (stateMatrix H M W state c).subst
      (Sum.elim Term.var (fun i => emb ((![work] : Fin 1 → OTerm alpha) i))) =
      stateFields H M W state work c := by
  unfold stateMatrix
  rw [witnessEmbedding,stateFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem acceptedStateSubst {alpha beta : Type} (H : Program 1) (M W : Program 2) (state c : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (AcceptedState H M W state c).subst (fun a => emb (ts a)) = AcceptedState H M W (state.subst ts) (c.subst ts) := by
  change (InternalFiniteBlocks.block (stateMatrix H M W state c)).subst _ = _
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold stateMatrix
  simp only [stateFieldsSubst,liftSubst,Term.subst,Sum.elim_inr]
  rfl

@[simp] theorem acceptedStateRename {alpha beta : Type} (H : Program 1) (M W : Program 2)
    (state c : OTerm alpha) (j : alpha → beta) :
    (AcceptedState H M W state c).relabel j = AcceptedState H M W (state.relabel j) (c.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AcceptedState H M W state c).subst (fun a => emb (.var (j a))) = _
  rw [acceptedStateSubst]
  simp only [← termRelabelAsSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceSyntaxProof
