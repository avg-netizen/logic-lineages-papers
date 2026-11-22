module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePrefixedRoundsMotiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePrefixedRoundsStepsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowMotiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePrefixedRoundsChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb z suc zRelabel sucRelabel bindEmbedding nextEmbedding liftBind varBind)
open ID1Completion.InternalTagArithmeticSupportProof (natInduction)
open ID1Completion.InternalAdditionLawsProof (liftNext varNext)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseDirectedRounds (rounds roundsTape)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparseRoundWindowMotiveProof (roundRename)
open NumberedWindowInternalSparsePrefixedRoundsMotiveProof
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePrefixedRoundsStepsProof (initial step prefixedRename)
open NumberedWindowInternalSparsePrefixedRoundsTargets

open ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity (included)
open ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InclusionProof (includedRename)
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)
attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem tapeRename {β : Type} (fuel vertices ctx ty seed : OTerm α) (j : α → β) :
    (fun i => (roundsTape fuel vertices ctx ty seed i).relabel j) =
      roundsTape (fuel.relabel j) (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) := by
  funext i
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun c =>
    Fin.cases ?_ (fun d => Fin.cases ?_ (fun e => Fin.elim0 e) d) c) b) a) i <;> rfl


private theorem baseRule (pred : ExactRetainedPredecessor) (E : Program 4) (vertices ctx ty seed upper : OTerm α)
    (guard : Nonempty (Derivation body Γ (memberGraph upper seed))) :
    Nonempty (Derivation body Γ (inside E z vertices ctx ty seed upper)) := by
  apply introduce
  intro β j Δ out keep r
  have g := renameInto guard j Δ keep
  rw [graphRename] at g
  rw [zRelabel] at r
  obtain ⟨g⟩ := g
  obtain ⟨r⟩ := r
  obtain ⟨law⟩ := initial pred E body β Δ (vertices.relabel j) (ctx.relabel j) (ty.relabel j)
    (seed.relabel j) (upper.relabel j) out
  exact ⟨Derivation.implicationElimination law (Derivation.conjunctionIntroduction r g)⟩

private theorem succAt (pred : ExactRetainedPredecessor) (E : Program 4) (out i vertices ctx ty seed upper later : OTerm α)
    (pre : Nonempty (Derivation body Γ (prefixed E vertices ctx ty upper later)))
    (old : Nonempty (Derivation body Γ (inside E i vertices ctx ty seed upper)))
    (run : Nonempty (Derivation body Γ (roundGraph E out (suc i) vertices ctx ty seed))) :
    Nonempty (Derivation body Γ (included out upper)) := by
  apply programCases (rounds E) (roundsTape i vertices ctx ty seed) _
  intro β j Δ before keep prior
  rw [includedRename]
  rw [tapeRename] at prior
  have ih := renameInto old j Δ keep
  rw [insideRename] at ih
  obtain ⟨inc⟩ := applyAt E _ _ _ _ _ _ before ih prior
  have current := renameInto run j Δ keep
  rw [roundRename,sucRelabel] at current
  have closed := renameInto pre j Δ keep
  rw [prefixedRename] at closed
  obtain ⟨current⟩ := current
  obtain ⟨prior⟩ := prior
  obtain ⟨closed⟩ := closed
  obtain ⟨law⟩ := step pred E body β Δ (vertices.relabel j) (ctx.relabel j) (ty.relabel j)
    (seed.relabel j) (upper.relabel j) (later.relabel j) (i.relabel j) before (out.relabel j)
  exact ⟨Derivation.implicationElimination law (Derivation.conjunctionIntroduction closed
    (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction prior current) inc))⟩

private theorem stepRule (pred : ExactRetainedPredecessor) (E : Program 4)
    (i vertices ctx ty seed upper later : OTerm α)
    (pre : Nonempty (Derivation body Γ (prefixed E vertices ctx ty upper later)))
    (old : Nonempty (Derivation body Γ (inside E i vertices ctx ty seed upper))) :
    Nonempty (Derivation body Γ (inside E (suc i) vertices ctx ty seed upper)) := by
  apply introduce
  intro β j Δ out keep r
  have prior := renameInto old j Δ keep
  rw [insideRename] at prior
  have closed := renameInto pre j Δ keep
  rw [prefixedRename] at closed
  rw [sucRelabel] at r
  exact succAt pred E out _ _ _ _ _ _ _ closed prior r

theorem exact_InitialInUpper : ExactInitialInUpper := initial
theorem exact_StepInUpper : ExactStepInUpper := step

theorem exact_RoundsInUpper : ExactRoundsInUpper := by
  intro pred E body α Γ vertices ctx ty seed upper later i out
  let A := (memberGraph upper seed ⊓ prefixed E vertices ctx ty upper later) ⊓ roundGraph E out i vertices ctx ty seed
  let Δ := A :: Γ
  have given : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have source := Derivation.conjunctionLeft (Derivation.conjunctionLeft given)
  have pre := Derivation.conjunctionRight (Derivation.conjunctionLeft given)
  let j : α → α ⊕ Fin 1 := Sum.inl
  let v : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let θ := inside E v (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) (upper.relabel j)
  have inst (n : OTerm α) : instantiate θ (emb n) = inside E n vertices ctx ty seed upper := by
    simp only [θ,instantiate,bindEmbedding,insideSubst,j,v,liftBind,varBind]
  have next : successorInstance θ = inside E (suc v) (vertices.relabel j) (ctx.relabel j) (ty.relabel j)
      (seed.relabel j) (upper.relabel j) := by
    simp only [θ,successorInstance,nextEmbedding,insideSubst,j,v,liftNext,varNext]
  obtain ⟨base⟩ := baseRule pred E vertices ctx ty seed upper ⟨source⟩
  have pre' := renameInto ⟨pre⟩ j (θ :: Δ.map weaken)
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [prefixedRename] at pre'
  obtain ⟨stepD⟩ := stepRule pred E v (vertices.relabel j) (ctx.relabel j) (ty.relabel j)
    (seed.relabel j) (upper.relabel j) (later.relabel j) pre' ⟨Derivation.hypothesis List.mem_cons_self⟩
  have every := Derivation.universalElimination (emb i)
    (natInduction θ (by rw [inst]; exact base) (by rw [next]; exact stepD))
  rw [inst] at every
  obtain ⟨result⟩ := applyAt E i vertices ctx ty seed upper out ⟨every⟩ ⟨Derivation.conjunctionRight given⟩
  exact ⟨Derivation.implicationIntroduction result⟩

#print axioms exact_InitialInUpper
#print axioms exact_StepInUpper
#print axioms exact_RoundsInUpper
end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePrefixedRoundsChecks
