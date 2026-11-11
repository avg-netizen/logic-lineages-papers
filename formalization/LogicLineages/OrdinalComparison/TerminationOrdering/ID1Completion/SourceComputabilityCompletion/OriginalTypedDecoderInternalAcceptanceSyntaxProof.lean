module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelSingletonProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceSyntaxProof
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
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalFuel OriginalTypedDecoderInternalAcceptance
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalFuelIterationSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem tripleSubst {alpha beta : Type} (a b c : OTerm alpha) (ts : alpha → OTerm beta) :
    (fun i : Fin 3 => (![a,b,c] i).subst ts) = ![a.subst ts,b.subst ts,c.subst ts] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i

theorem termAcceptedSubst {alpha beta : Type} (H : Program 1) (typ raw gamma : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (TermAccepted H typ raw gamma).subst (fun a => emb (ts a)) =
      TermAccepted H (typ.subst ts) (raw.subst ts) (gamma.subst ts) := by
  simp only [TermAccepted,programSubst,tripleSubst,numeral,sucSubst,zSubst]

@[simp] theorem termAcceptedRename {alpha beta : Type} (H : Program 1)
    (typ raw gamma : OTerm alpha) (j : alpha → beta) :
    (TermAccepted H typ raw gamma).relabel j =
      TermAccepted H (typ.relabel j) (raw.relabel j) (gamma.relabel j) := by
  simp only [TermAccepted,programRename,oneRename,OriginalTypedDecoderInternalFuelSingletonProof.tripleRename]

theorem argumentsAcceptedSubst {alpha beta : Type} (H : Program 1) (types raw gamma : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (ArgumentsAccepted H types raw gamma).subst (fun a => emb (ts a)) =
      ArgumentsAccepted H (types.subst ts) (raw.subst ts) (gamma.subst ts) := by
  simp only [ArgumentsAccepted,programSubst,tripleSubst,numeral,sucSubst,zSubst]

@[simp] theorem argumentsAcceptedRename {alpha beta : Type} (H : Program 1)
    (types raw gamma : OTerm alpha) (j : alpha → beta) :
    (ArgumentsAccepted H types raw gamma).relabel j =
      ArgumentsAccepted H (types.relabel j) (raw.relabel j) (gamma.relabel j) := by
  simp only [ArgumentsAccepted,programRename,oneRename,OriginalTypedDecoderInternalFuelSingletonProof.tripleRename]

def stateFields {alpha : Type} (H : Program 1) (state work : OTerm alpha) : Formula alpha :=
  StepLive state work ⊓ WorkAccepted H work

def stateMatrix {alpha : Type} (H : Program 1) (state : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  stateFields H (state.relabel Sum.inl) (.var (.inr 0))

theorem stateFieldsSubst {alpha beta : Type} (H : Program 1) (state work : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (stateFields H state work).subst (fun a => emb (ts a)) =
      stateFields H (state.subst ts) (work.subst ts) := by
  simp only [stateFields,conjunctionSubst,stepLiveSubst,workAcceptedSubst]

theorem stateMatrixWitness {alpha : Type} (H : Program 1) (state work : OTerm alpha) :
    (stateMatrix H state).subst
      (Sum.elim Term.var (fun i => emb ((![work] : Fin 1 → OTerm alpha) i))) =
      stateFields H state work := by
  unfold stateMatrix
  rw [witnessEmbedding,stateFieldsSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem acceptedStateSubst {alpha beta : Type} (H : Program 1) (state : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (AcceptedState H state).subst (fun a => emb (ts a)) = AcceptedState H (state.subst ts) := by
  change (InternalFiniteBlocks.block (stateMatrix H state)).subst _ = _
  unfold InternalFiniteBlocks.block
  rw [exsSubst,bindSubst,liftedEmbedding]
  unfold stateMatrix
  simp only [stateFieldsSubst,liftSubst,Term.subst,Sum.elim_inr]
  rfl

@[simp] theorem acceptedStateRename {alpha beta : Type} (H : Program 1)
    (state : OTerm alpha) (j : alpha → beta) :
    (AcceptedState H state).relabel j = AcceptedState H (state.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AcceptedState H state).subst (fun a => emb (.var (j a))) = _
  rw [acceptedStateSubst]
  simp only [← termRelabelAsSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceSyntaxProof
