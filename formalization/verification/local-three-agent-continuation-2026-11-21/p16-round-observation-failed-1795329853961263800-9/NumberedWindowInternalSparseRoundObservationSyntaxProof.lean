module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundObservationTargets
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
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundObservationSyntaxProof
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
open NumberedWindowInternalSparseRoundObservationTargets
attribute [local irreducible] programGraph

open NumberedWindowInternalSparseDirectedSeen (acceptEdge edgeTape)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
variable (E : Program 4) (M : Program 5)
variable {α : Type}

theorem observedSubst {β : Type} (ctx dom cod arg k m : OTerm α) (ts : α → OTerm β) :
    (observed M ctx dom cod arg k m).subst (fun x => emb (ts x)) =
      observed M (ctx.subst ts) (dom.subst ts) (cod.subst ts) (arg.subst ts) (k.subst ts) (m.subst ts) := by
  have tape : (fun i => ((![k,ctx,dom,cod,arg] : Fin 5 → OTerm α) i).subst ts) =
      ![k.subst ts,ctx.subst ts,dom.subst ts,cod.subst ts,arg.subst ts] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl Fin.elim0)))) i
  simp only [observed,programSubst,tape]

theorem observedRename {β : Type} (ctx dom cod arg k m : OTerm α) (j : α → β) :
    (observed M ctx dom cod arg k m).relabel j =
      observed M (ctx.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j) (k.relabel j) (m.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (observed M ctx dom cod arg k m).subst (fun x => emb (.var (j x))) = _
  rw [observedSubst]
  simp only [← termRelabelAsSubst]

theorem edgeSubst {β : Type} (ctx ty f g : OTerm α) (ts : α → OTerm β) :
    (acceptEdge E ctx ty f g).subst (fun x => emb (ts x)) =
      acceptEdge E (ctx.subst ts) (ty.subst ts) (f.subst ts) (g.subst ts) := by
  have tape : (fun i => (edgeTape ctx ty f g i).subst ts) =
      edgeTape (ctx.subst ts) (ty.subst ts) (f.subst ts) (g.subst ts) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl Fin.elim0))) i
  simp only [acceptEdge,programSubst,tape,sucSubst,zSubst]

theorem closedSubst {β : Type} (ctx ty dom cod arg m : OTerm α) (ts : α → OTerm β) :
    (closed E M ctx ty dom cod arg m).subst (fun x => emb (ts x)) =
      closed E M (ctx.subst ts) (ty.subst ts) (dom.subst ts) (cod.subst ts) (arg.subst ts) (m.subst ts) := by
  unfold closed edgeRow
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,conjunctionSubst,observedSubst,edgeSubst,liftSubst,Term.subst,Sum.elim_inr]

theorem sourceSubst {β : Type} (ctx ty dom cod arg seed m : OTerm α) (ts : α → OTerm β) :
    (source E M ctx ty dom cod arg seed m).subst (fun x => emb (ts x)) =
      source E M (ctx.subst ts) (ty.subst ts) (dom.subst ts) (cod.subst ts) (arg.subst ts) (seed.subst ts) (m.subst ts) := by
  simp only [source,conjunctionSubst,closedSubst,observedSubst]

theorem sourceRename {β : Type} (ctx ty dom cod arg seed m : OTerm α) (j : α → β) :
    (source E M ctx ty dom cod arg seed m).relabel j =
      source E M (ctx.relabel j) (ty.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j) (seed.relabel j) (m.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (source E M ctx ty dom cod arg seed m).subst (fun x => emb (.var (j x))) = _
  rw [sourceSubst]
  simp only [← termRelabelAsSubst]

theorem applyEdge {body : Positive (Fin 1)} {Γ : List (Formula α)} (ctx ty dom cod arg m f g : OTerm α)
    (law : Nonempty (Derivation body Γ (closed E M ctx ty dom cod arg m)))
    (edge : Derivation body Γ (acceptEdge E ctx ty f g))
    (atF : Derivation body Γ (observed M ctx dom cod arg f m)) :
    Nonempty (Derivation body Γ (observed M ctx dom cod arg g m)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body α 2 Γ (edgeRow E M ctx ty dom cod arg m)
    (fun i => emb (![f,g] i)) law
  have he : (Sum.elim Term.var (fun i => emb (![f,g] i))) =
      (fun a => emb (Sum.elim Term.var ![f,g] a)) := by
    funext x
    cases x <;> rfl
  simp only [edgeRow,he,impSubst,conjunctionSubst,edgeSubst,observedSubst,witnessLift,Term.subst,Sum.elim_inr] at h
  exact ⟨Derivation.implicationElimination h (Derivation.conjunctionIntroduction edge atF)⟩

def matrix {alpha : Type} (elapsed : OTerm alpha) : Formula (alpha ⊕ Fin 10) :=
  (inputs E M (elapsed.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5)) (.var (.inr 6)) (.var (.inr 7)) (.var (.inr 8)) (.var (.inr 9))).imp
    (observed M (.var (.inr 1)) (.var (.inr 7)) (.var (.inr 8)) (.var (.inr 9)) (.var (.inr 5)) (.var (.inr 6)))

def AtCount {alpha : Type} (elapsed : OTerm alpha) : Formula alpha := allBlock (matrix E M elapsed)

theorem inputsSubst {alpha beta : Type} (elapsed vertices ctx ty seed out k m dom cod arg : OTerm alpha) (ts : alpha → OTerm beta) :
  (inputs E M elapsed vertices ctx ty seed out k m dom cod arg).subst (fun a => emb (ts a)) =
    inputs E M (elapsed.subst ts) (vertices.subst ts) (ctx.subst ts) (ty.subst ts) (seed.subst ts) (out.subst ts) (k.subst ts) (m.subst ts) (dom.subst ts) (cod.subst ts) (arg.subst ts) := by
  simp only [inputs,conjunctionSubst,roundSubst,sourceSubst,memberSubst]

theorem atCountSubst {alpha beta : Type} (elapsed : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtCount E M elapsed).subst (fun a => emb (ts a)) = AtCount E M (elapsed.subst ts) := by
  unfold AtCount matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,inputsSubst,observedSubst,liftSubst,Term.subst,Sum.elim_inr]
@[simp] theorem atCountRename {alpha beta : Type} (elapsed : OTerm alpha) (j : alpha → beta) :
    (AtCount E M elapsed).relabel j = AtCount E M (elapsed.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtCount E M elapsed).subst (fun a => emb (.var (j a))) = _
  rw [atCountSubst]
  simp only [← termRelabelAsSubst]
theorem matrixWitness {alpha : Type}
    (elapsed vertices ctx ty seed out k m dom cod arg : OTerm alpha) :
    (matrix E M elapsed).subst (Sum.elim Term.var
      (fun i => emb (![vertices,ctx,ty,seed,out,k,m,dom,cod,arg] i))) =
      (inputs E M elapsed vertices ctx ty seed out k m dom cod arg).imp
        (observed M ctx dom cod arg k m) := by
  have he : (Sum.elim Term.var
      (fun i => emb (![vertices,ctx,ty,seed,out,k,m,dom,cod,arg] i))) =
      (fun a => emb (Sum.elim Term.var ![vertices,ctx,ty,seed,out,k,m,dom,cod,arg] a)) := by
    funext a
    cases a <;> rfl
  unfold matrix
  rw [he]
  simp only [impSubst,inputsSubst,observedSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem applyAt {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
    (elapsed vertices ctx ty seed out k m dom cod arg : OTerm alpha)
    (row : Nonempty (Derivation body Delta (AtCount E M elapsed)))
    (data : Nonempty (Derivation body Delta (inputs E M elapsed vertices ctx ty seed out k m dom cod arg))) :
    Nonempty (Derivation body Delta (observed M ctx dom cod arg k m)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 10 Delta (matrix E M elapsed)
    (fun i => emb (![vertices,ctx,ty,seed,out,k,m,dom,cod,arg] i)) row
  rw [matrixWitness] at h
  obtain ⟨d⟩ := data
  exact ⟨Derivation.implicationElimination h d⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundObservationSyntaxProof
