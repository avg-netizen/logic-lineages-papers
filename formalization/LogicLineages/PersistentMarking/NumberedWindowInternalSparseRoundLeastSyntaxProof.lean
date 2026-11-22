module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundLeastTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowMotiveProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.CompareSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundLeastSyntaxProof
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
open NumberedWindowInternalSparseRoundLeastTargets
attribute [local irreducible] programGraph

open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
variable (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
variable {α : Type}

theorem leastSubst {β : Type} (ctx ty seed x : OTerm α) (ts : α → OTerm β) :
    (leastGraph C X W s ctx ty seed x).subst (fun a => emb (ts a)) =
    leastGraph C X W s (ctx.subst ts) (ty.subst ts) (seed.subst ts) (x.subst ts) := by
  have tape : (fun i => ((![ctx,ty,seed] : Fin 3 → OTerm α) i).subst ts) = ![ctx.subst ts,ty.subst ts,seed.subst ts] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
  simp only [leastGraph,programSubst,sucSubst,tape]

def matrix {alpha : Type} (elapsed : OTerm alpha) : Formula (alpha ⊕ Fin 7) :=
  (inputs C X W s (elapsed.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5)) (.var (.inr 6))).imp
    (leastGraph C X W s (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 5)) (.var (.inr 6)))

def AtCount {alpha : Type} (elapsed : OTerm alpha) : Formula alpha := allBlock (matrix C X W s elapsed)

theorem inputsSubst {alpha beta : Type} (elapsed vertices ctx ty seed out k m : OTerm alpha) (ts : alpha → OTerm beta) :
  (inputs C X W s elapsed vertices ctx ty seed out k m).subst (fun a => emb (ts a)) =
    inputs C X W s (elapsed.subst ts) (vertices.subst ts) (ctx.subst ts) (ty.subst ts) (seed.subst ts) (out.subst ts) (k.subst ts) (m.subst ts) := by
  simp only [inputs,conjunctionSubst,roundSubst,leastSubst,memberSubst]

theorem atCountSubst {alpha beta : Type} (elapsed : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtCount C X W s elapsed).subst (fun a => emb (ts a)) = AtCount C X W s (elapsed.subst ts) := by
  unfold AtCount matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,inputsSubst,leastSubst,liftSubst,Term.subst,Sum.elim_inr]
@[simp] theorem atCountRename {alpha beta : Type} (elapsed : OTerm alpha) (j : alpha → beta) :
    (AtCount C X W s elapsed).relabel j = AtCount C X W s (elapsed.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtCount C X W s elapsed).subst (fun a => emb (.var (j a))) = _
  rw [atCountSubst]
  simp only [← termRelabelAsSubst]
theorem matrixWitness {alpha : Type}
    (elapsed vertices ctx ty seed out k m : OTerm alpha) :
    (matrix C X W s elapsed).subst (Sum.elim Term.var
      (fun i => emb (![vertices,ctx,ty,seed,out,k,m] i))) =
      (inputs C X W s elapsed vertices ctx ty seed out k m).imp
        (leastGraph C X W s ctx ty k m) := by
  have he : (Sum.elim Term.var
      (fun i => emb (![vertices,ctx,ty,seed,out,k,m] i))) =
      (fun a => emb (Sum.elim Term.var ![vertices,ctx,ty,seed,out,k,m] a)) := by
    funext a
    cases a <;> rfl
  unfold matrix
  rw [he]
  simp only [impSubst,inputsSubst,leastSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem applyAt {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
    (elapsed vertices ctx ty seed out k m : OTerm alpha)
    (row : Nonempty (Derivation body Delta (AtCount C X W s elapsed)))
    (data : Nonempty (Derivation body Delta (inputs C X W s elapsed vertices ctx ty seed out k m))) :
    Nonempty (Derivation body Delta (leastGraph C X W s ctx ty k m)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 7 Delta (matrix C X W s elapsed)
    (fun i => emb (![vertices,ctx,ty,seed,out,k,m] i)) row
  rw [matrixWitness] at h
  obtain ⟨d⟩ := data
  exact ⟨Derivation.implicationElimination h d⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundLeastSyntaxProof
