module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationBoundSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelInclusionSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb eqnSubst eqnRelabel zSubst zRelabel sucRelabel bindEmbedding bindTerm nextEmbedding nextTerm)
open InternalTagArithmeticSupportProof
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight)
open InternalQuotientComparisonProof (orLeft orRight)
open InternalOriginalPairingOrderArithmeticProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalFiniteBlocksSubstitutionProof InternalAdditionLawsProof InternalClosedPrograms
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalLogicSyntaxProof

def stepResult {alpha : Type} (H : Program 1) (out initial : OTerm alpha) : Formula alpha :=
  equal out z ⊔ graph1 (OriginalTypedDecoder.transition H) out initial

def runResult {alpha : Type} (H : Program 1) (out count initial : OTerm alpha) : Formula alpha :=
  equal out z ⊔ graph2 (OriginalTypedDecoder.iterate H) out count initial

theorem stepResultSubst {alpha beta : Type} (H : Program 1) (out initial : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (stepResult H out initial).subst (fun a => emb (ts a)) =
      stepResult H (out.subst ts) (initial.subst ts) := by
  simp only [stepResult,orSubst,equalEqn,eqnSubst,zSubst,graph1,programSubst,consTermSubst,emptySubst]

@[simp] theorem stepResultRename {alpha beta : Type} (H : Program 1) (out initial : OTerm alpha)
    (j : alpha → beta) :
    (stepResult H out initial).relabel j = stepResult H (out.relabel j) (initial.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (stepResult H out initial).subst (fun a => emb (.var (j a))) = _
  rw [stepResultSubst]
  simp only [← termRelabelAsSubst]

theorem runResultSubst {alpha beta : Type} (H : Program 1) (out count initial : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (runResult H out count initial).subst (fun a => emb (ts a)) =
      runResult H (out.subst ts) (count.subst ts) (initial.subst ts) := by
  simp only [runResult,orSubst,equalEqn,eqnSubst,zSubst,graph2,programSubst,consTermSubst,emptySubst]

@[simp] theorem runResultRename {alpha beta : Type} (H : Program 1) (out count initial : OTerm alpha)
    (j : alpha → beta) :
    (runResult H out count initial).relabel j =
      runResult H (out.relabel j) (count.relabel j) (initial.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (runResult H out count initial).subst (fun a => emb (.var (j a))) = _
  rw [runResultSubst]
  simp only [← termRelabelAsSubst]

/-- All original raw initial states, outputs and separate context values are
inside the arithmetic induction invariant, at the identical fuel. -/
def inclusionBody {alpha : Type} (H : Program 1) (M contextWindow : Program 2)
    (count : OTerm alpha) : Formula (alpha ⊕ Fin 3) :=
  (graph3 (OriginalUniverseDecoder.iterate H M contextWindow) (.var (.inr 1))
    (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 2))).imp
      (runResult H (.var (.inr 1)) (count.relabel Sum.inl) (.var (.inr 0)))

def inclusionRow {alpha : Type} (H : Program 1) (M contextWindow : Program 2)
    (count : OTerm alpha) : Formula alpha := allBlock (inclusionBody H M contextWindow count)

theorem inclusionRowSubst {alpha beta : Type} (H : Program 1) (M contextWindow : Program 2)
    (count : OTerm alpha) (ts : alpha → OTerm beta) :
    (inclusionRow H M contextWindow count).subst (fun a => emb (ts a)) =
      inclusionRow H M contextWindow (count.subst ts) := by
  unfold inclusionRow inclusionBody
  rw [allBlockSubst,liftedEmbedding,impSubst]
  simp only [graph3,programSubst,consTermSubst,emptySubst,runResultSubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem inclusionRowRename {alpha beta : Type} (H : Program 1) (M contextWindow : Program 2)
    (count : OTerm alpha) (j : alpha → beta) :
    (inclusionRow H M contextWindow count).relabel j =
      inclusionRow H M contextWindow (count.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (inclusionRow H M contextWindow count).subst (fun a => emb (.var (j a))) = _
  rw [inclusionRowSubst]
  simp only [← termRelabelAsSubst]

theorem inclusionBodyWitness {alpha : Type} (H : Program 1) (M contextWindow : Program 2)
    (count initial out c : OTerm alpha) :
    (inclusionBody H M contextWindow count).subst
      (Sum.elim Term.var (fun i => emb (![initial,out,c] i))) =
      (graph3 (OriginalUniverseDecoder.iterate H M contextWindow) out count initial c).imp
        (runResult H out count initial) := by
  unfold inclusionBody
  rw [witnessEmbedding,impSubst]
  simp only [graph3,programSubst,consTermSubst,emptySubst,runResultSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem inclusionInstantiate {alpha : Type} (H : Program 1) (M contextWindow : Program 2)
    (count : OTerm (alpha ⊕ Fin 1)) (v : OTerm alpha) :
    instantiate (inclusionRow H M contextWindow count) (emb v) =
      inclusionRow H M contextWindow (count.subst (bindTerm v)) := by
  rw [instantiate,bindEmbedding,inclusionRowSubst]

theorem inclusionSuccessor {alpha : Type} (H : Program 1) (M contextWindow : Program 2)
    (count : OTerm (alpha ⊕ Fin 1)) :
    successorInstance (inclusionRow H M contextWindow count) =
      inclusionRow H M contextWindow (count.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,inclusionRowSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelInclusionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelInclusionSyntaxProof
