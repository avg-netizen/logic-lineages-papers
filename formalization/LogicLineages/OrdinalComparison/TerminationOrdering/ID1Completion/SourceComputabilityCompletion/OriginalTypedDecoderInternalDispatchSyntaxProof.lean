module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalVariableSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLambdaSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalApplicationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalOrdinarySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalNumberedSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalConsSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalDispatchSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalRecursionClosureSyntaxProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalTagArithmeticSyntaxProof (emb)
open OriginalTypedDecoderStepSpecification
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTypedDecoderInternalVariableSyntaxProof
open OriginalTypedDecoderInternalLambdaSyntaxProof
open OriginalTypedDecoderInternalApplicationSyntaxProof
open OriginalTypedDecoderInternalOrdinarySyntaxProof
open OriginalTypedDecoderInternalNumberedSyntaxProof
open OriginalTypedDecoderInternalConsSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof

theorem stepTermDispatchSubst {alpha beta : Type} (H : Program 1) (out gamma typ tag payload rest : OTerm alpha) (ts : alpha → OTerm beta) :
    (StepTermDispatch H out gamma typ tag payload rest).subst (fun a => emb (ts a)) = StepTermDispatch H (out.subst ts) (gamma.subst ts) (typ.subst ts) (tag.subst ts) (payload.subst ts) (rest.subst ts) := by
  simp only [StepTermDispatch,orSubst,conjunctionSubst,equalSubst,numeralSubst,stepVariableSubst,stepLambdaSubst,stepApplicationSubst,stepBottomSubst,stepOrdinarySubst,stepNumberedSubst,stepUnknownTagSubst,InternalOriginalOrderSyntaxProof.notSubst]

@[simp] theorem stepTermDispatchRename {alpha beta : Type} (H : Program 1) (out gamma typ tag payload rest : OTerm alpha) (j : alpha → beta) :
    (StepTermDispatch H out gamma typ tag payload rest).relabel j = StepTermDispatch H (out.relabel j) (gamma.relabel j) (typ.relabel j) (tag.relabel j) (payload.relabel j) (rest.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (StepTermDispatch H out gamma typ tag payload rest).subst (fun a => emb (.var (j a))) = _
  rw [stepTermDispatchSubst]
  simp only [← termRelabelAsSubst]

theorem stepArgumentsDispatchSubst {alpha beta : Type} (out gamma typ tag payload rest : OTerm alpha) (ts : alpha → OTerm beta) :
    (StepArgumentsDispatch out gamma typ tag payload rest).subst (fun a => emb (ts a)) = StepArgumentsDispatch (out.subst ts) (gamma.subst ts) (typ.subst ts) (tag.subst ts) (payload.subst ts) (rest.subst ts) := by
  simp only [StepArgumentsDispatch,orSubst,conjunctionSubst,equalSubst,numeralSubst,stepArgumentsNilSubst,stepArgumentsConsSubst,stepUnknownTagSubst,InternalOriginalOrderSyntaxProof.notSubst]

@[simp] theorem stepArgumentsDispatchRename {alpha beta : Type} (out gamma typ tag payload rest : OTerm alpha) (j : alpha → beta) :
    (StepArgumentsDispatch out gamma typ tag payload rest).relabel j = StepArgumentsDispatch (out.relabel j) (gamma.relabel j) (typ.relabel j) (tag.relabel j) (payload.relabel j) (rest.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (StepArgumentsDispatch out gamma typ tag payload rest).subst (fun a => emb (.var (j a))) = _
  rw [stepArgumentsDispatchSubst]
  simp only [← termRelabelAsSubst]

theorem stepModeDispatchSubst {alpha beta : Type} (H : Program 1) (out mode gamma typ tag payload rest : OTerm alpha) (ts : alpha → OTerm beta) :
    (StepModeDispatch H out mode gamma typ tag payload rest).subst (fun a => emb (ts a)) = StepModeDispatch H (out.subst ts) (mode.subst ts) (gamma.subst ts) (typ.subst ts) (tag.subst ts) (payload.subst ts) (rest.subst ts) := by
  simp only [StepModeDispatch,orSubst,conjunctionSubst,equalSubst,numeralSubst,stepTermDispatchSubst,stepArgumentsDispatchSubst,InternalOriginalOrderSyntaxProof.notSubst]

@[simp] theorem stepModeDispatchRename {alpha beta : Type} (H : Program 1) (out mode gamma typ tag payload rest : OTerm alpha) (j : alpha → beta) :
    (StepModeDispatch H out mode gamma typ tag payload rest).relabel j = StepModeDispatch H (out.relabel j) (mode.relabel j) (gamma.relabel j) (typ.relabel j) (tag.relabel j) (payload.relabel j) (rest.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (StepModeDispatch H out mode gamma typ tag payload rest).subst (fun a => emb (.var (j a))) = _
  rw [stepModeDispatchSubst]
  simp only [← termRelabelAsSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalDispatchSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalDispatchSyntaxProof
