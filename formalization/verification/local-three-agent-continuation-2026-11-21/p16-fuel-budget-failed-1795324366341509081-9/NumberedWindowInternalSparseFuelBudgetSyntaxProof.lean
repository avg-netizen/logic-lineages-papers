module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFuelBudgetTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowMotiveProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.CompareSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFuelBudgetSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.SourceComputabilityCompletion
open ID1Completion.SourceComputabilityCompletion.Continuation20261114
open PrimaryFiniteDescent (budget)
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof
open InternalApplicationCertificateConstructors (graph2)
open InternalApplicationValidityStackAppendSyntaxProof (graph2Subst)
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof InternalClosedPrograms
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open PrimaryMonotonicity.InclusionProof
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open InternalStrongInduction
open PrimaryUncoveredCount.CompareSyntaxProof (boundedSubst)
open PrimaryUncoveredCount.OrderProof (boundedRename)
open NumberedWindowInternalSparseRoundWindowMotiveProof (roundSubst)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (unarySubst)
open NumberedWindowInternalSparseFuelBudgetTargets
attribute [local irreducible] programGraph

def matrix {alpha : Type} (E : Program 4) (elapsed : OTerm alpha) : Formula (alpha ⊕ Fin 8) :=
  (inputs E (elapsed.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5)) (.var (.inr 6)) (.var (.inr 7))).imp
    (budget (elapsed.relabel Sum.inl) (.var (.inr 4)) (.var (.inr 7)) (.var (.inr 5)) (.var (.inr 6)))

def AtCount {alpha : Type} (E : Program 4) (elapsed : OTerm alpha) : Formula alpha := allBlock (matrix E elapsed)

@[simp] theorem budgetRename {alpha beta : Type}
    (elapsed initialRemaining remaining out next : OTerm alpha) (j : alpha → beta) :
    (budget elapsed initialRemaining remaining out next).relabel j =
      budget (elapsed.relabel j) (initialRemaining.relabel j) (remaining.relabel j)
        (out.relabel j) (next.relabel j) := by
  simp only [budget,PrimaryExpansionSoundness.AppendSyntaxProof.orRename,includedRename,boundedRename,addRelabel]
theorem budgetSubst {alpha beta : Type}
    (elapsed initialRemaining remaining out next : OTerm alpha) (ts : alpha → OTerm beta) :
    (budget elapsed initialRemaining remaining out next).subst (fun a => emb (ts a)) =
      budget (elapsed.subst ts) (initialRemaining.subst ts) (remaining.subst ts)
        (out.subst ts) (next.subst ts) := by
  simp only [budget,OriginalTypedDecoderInternalLogicSyntaxProof.orSubst,includedSubst,boundedSubst,addSubst]
theorem inputsSubst {alpha beta : Type} (E : Program 4) (elapsed vertices ctx ty seed size before after count : OTerm alpha) (ts : alpha → OTerm beta) :
  (inputs E elapsed vertices ctx ty seed size before after count).subst (fun a => emb (ts a)) =
    inputs E (elapsed.subst ts) (vertices.subst ts) (ctx.subst ts) (ty.subst ts) (seed.subst ts) (size.subst ts) (before.subst ts) (after.subst ts) (count.subst ts) := by
  simp only [inputs,runsAt,conjunctionSubst,roundSubst,unarySubst,graph2Subst,sucSubst]

theorem atCountSubst {alpha beta : Type} (E : Program 4) (elapsed : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtCount E elapsed).subst (fun a => emb (ts a)) = AtCount E (elapsed.subst ts) := by
  unfold AtCount matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,inputsSubst,budgetSubst,liftSubst,Term.subst,Sum.elim_inr]
@[simp] theorem atCountRename {alpha beta : Type} (E : Program 4) (elapsed : OTerm alpha) (j : alpha → beta) :
    (AtCount E elapsed).relabel j = AtCount E (elapsed.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtCount E elapsed).subst (fun a => emb (.var (j a))) = _
  rw [atCountSubst]
  simp only [← termRelabelAsSubst]
theorem matrixWitness {alpha : Type} (E : Program 4)
    (elapsed vertices ctx ty seed size before after count : OTerm alpha) :
    (matrix E elapsed).subst (Sum.elim Term.var
      (fun i => emb (![vertices,ctx,ty,seed,size,before,after,count] i))) =
      (inputs E elapsed vertices ctx ty seed size before after count).imp
        (budget elapsed size count before after) := by
  have he : (Sum.elim Term.var
      (fun i => emb (![vertices,ctx,ty,seed,size,before,after,count] i))) =
      (fun a => emb (Sum.elim Term.var ![vertices,ctx,ty,seed,size,before,after,count] a)) := by
    funext a
    cases a <;> rfl
  unfold matrix
  rw [he]
  simp only [impSubst,inputsSubst,budgetSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem applyAt {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
    (E : Program 4) (elapsed vertices ctx ty seed size before after count : OTerm alpha)
    (row : Nonempty (Derivation body Delta (AtCount E elapsed)))
    (data : Nonempty (Derivation body Delta (inputs E elapsed vertices ctx ty seed size before after count))) :
    Nonempty (Derivation body Delta (budget elapsed size count before after)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 8 Delta (matrix E elapsed)
    (fun i => emb (![vertices,ctx,ty,seed,size,before,after,count] i)) row
  rw [matrixWitness] at h
  obtain ⟨d⟩ := data
  exact ⟨Derivation.implicationElimination h d⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFuelBudgetSyntaxProof
