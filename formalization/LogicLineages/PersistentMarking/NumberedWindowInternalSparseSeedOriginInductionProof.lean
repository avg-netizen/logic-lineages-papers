module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedOriginMotiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundOriginChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowMotiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedOriginInductionProof
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
open NumberedWindowInternalSparseSeedOriginMotiveProof
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseRoundOriginChecks (exact_ZeroRoundOrigin exact_SuccessorRoundOrigin)
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)
open NumberedWindowInternalSparseDirectedSeen (seenWitness witnessRow)
open NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof (witnessBinder witnessUnfold)
open NumberedWindowInternalSparseSeedOriginTargets

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem tapeRename {β : Type} (fuel vertices ctx ty seed : OTerm α) (j : α → β) :
    (fun i => (roundsTape fuel vertices ctx ty seed i).relabel j) =
      roundsTape (fuel.relabel j) (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) := by
  funext i
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun c =>
    Fin.cases ?_ (fun d => Fin.cases ?_ (fun e => Fin.elim0 e) d) c) b) a) i <;> rfl

private theorem baseAt (paid : ExactRetainedPredecessor) (E : Program 4)
    (out vertices ctx ty seed : OTerm α)
    (run : Nonempty (Derivation body Γ (roundGraph E out z vertices ctx ty seed))) :
    Nonempty (Derivation body Γ (originAt vertices seed out)) := by
  apply originIntro
  intro β j Δ k keep hit
  have r := renameInto run j Δ keep
  rw [roundRename,zRelabel] at r
  obtain ⟨r⟩ := r
  obtain ⟨law⟩ := exact_ZeroRoundOrigin paid E body β Δ (out.relabel j) (vertices.relabel j)
    (ctx.relabel j) (ty.relabel j) (seed.relabel j) k
  exact ⟨Derivation.conjunctionLeft (Derivation.implicationElimination
    (Derivation.conjunctionLeft (Derivation.implicationElimination law r)) hit)⟩

private theorem baseRule (paid : ExactRetainedPredecessor) (E : Program 4) (vertices ctx ty seed : OTerm α) :
    Nonempty (Derivation body Γ (originRound E z vertices ctx ty seed)) := by
  apply introduce
  intro β j Δ out keep r
  rw [zRelabel] at r
  exact baseAt paid E out _ _ _ _ r

private theorem sourceOfWitness (E : Program 4) (before vertices ctx ty seed k : OTerm α)
    (old : Nonempty (Derivation body Γ (originAt vertices seed before)))
    (witness : Derivation body Γ (seenWitness E before ctx ty k)) :
    Nonempty (Derivation body Γ (memberGraph vertices seed)) := by
  rw [witnessUnfold] at witness
  let j : α → α ⊕ Fin 1 := Sum.inl
  let w : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let Θ := witnessBinder E before ctx ty k :: Γ.map weaken
  have r := renameInto old j Θ (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [originAtRename] at r
  obtain ⟨r⟩ := r
  have atW : Derivation body Θ (witnessRow E (before.relabel j) (ctx.relabel j)
      (ty.relabel j) w (k.relabel j)) := Derivation.hypothesis List.mem_cons_self
  obtain ⟨source⟩ := atMember (vertices.relabel j) (seed.relabel j) (before.relabel j) w r
    (Derivation.conjunctionLeft atW)
  have final : Derivation body Θ (weaken (memberGraph vertices seed)) := by
    change Derivation body Θ ((memberGraph vertices seed).relabel j)
    rwa [graphRename]
  exact ⟨Derivation.existentialElimination witness final⟩

private theorem advance (paid : ExactRetainedPredecessor) (E : Program 4)
    (before out fuel vertices ctx ty seed : OTerm α)
    (old : Nonempty (Derivation body Γ (originAt vertices seed before)))
    (prior : Nonempty (Derivation body Γ (roundGraph E before fuel vertices ctx ty seed)))
    (current : Nonempty (Derivation body Γ (roundGraph E out (suc fuel) vertices ctx ty seed))) :
    Nonempty (Derivation body Γ (originAt vertices seed out)) := by
  apply originIntro
  intro β j Δ k keep hit
  have ih := renameInto old j Δ keep
  have p := renameInto prior j Δ keep
  have r := renameInto current j Δ keep
  rw [originAtRename] at ih
  rw [roundRename] at p
  rw [roundRename,sucRelabel] at r
  obtain ⟨r⟩ := r
  obtain ⟨p⟩ := p
  obtain ⟨law⟩ := exact_SuccessorRoundOrigin paid E body β Δ (before.relabel j) (out.relabel j)
    (fuel.relabel j) (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) k
  have earlier := Derivation.implicationElimination (Derivation.conjunctionLeft
    (Derivation.implicationElimination law (Derivation.conjunctionIntroduction p r))) hit
  exact sourceOfWitness E _ _ _ _ _ k ih (Derivation.conjunctionRight earlier)

private theorem succAt (paid : ExactRetainedPredecessor) (E : Program 4) (out fuel vertices ctx ty seed : OTerm α)
    (old : Nonempty (Derivation body Γ (originRound E fuel vertices ctx ty seed)))
    (run : Nonempty (Derivation body Γ (roundGraph E out (suc fuel) vertices ctx ty seed))) :
    Nonempty (Derivation body Γ (originAt vertices seed out)) := by
  apply programCases (rounds E) (roundsTape fuel vertices ctx ty seed) _
  intro β j Δ before keep prior
  rw [originAtRename]
  rw [tapeRename] at prior
  have ih := renameInto old j Δ keep
  rw [originRoundRename] at ih
  obtain ⟨yes⟩ := applyAt E _ _ _ _ _ before ih prior
  have current := renameInto run j Δ keep
  rw [roundRename,sucRelabel] at current
  exact advance paid E before (out.relabel j) (fuel.relabel j) (vertices.relabel j) (ctx.relabel j)
    (ty.relabel j) (seed.relabel j) ⟨yes⟩ prior current

private theorem stepRule (paid : ExactRetainedPredecessor) (E : Program 4)
    (fuel vertices ctx ty seed : OTerm α) (old : Nonempty (Derivation body Γ (originRound E fuel vertices ctx ty seed))) :
    Nonempty (Derivation body Γ (originRound E (suc fuel) vertices ctx ty seed)) := by
  apply introduce
  intro β j Δ out keep r
  have prior := renameInto old j Δ keep
  rw [originRoundRename] at prior
  rw [sucRelabel] at r
  exact succAt paid E out _ _ _ _ _ prior r

theorem roundSource : ExactRoundSeedOrigin := by
  intro paid E body α Γ fuel vertices ctx ty seed out k
  let A := roundGraph E out fuel vertices ctx ty seed ⊓ memberGraph out k
  let Δ := A :: Γ
  have given : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  let j : α → α ⊕ Fin 1 := Sum.inl
  let v : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let θ := originRound E v (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j)
  have inst (n : OTerm α) : instantiate θ (emb n) = originRound E n vertices ctx ty seed := by
    simp only [θ,instantiate,bindEmbedding,originRoundSubst,j,v,liftBind,varBind]
  have next : successorInstance θ = originRound E (suc v) (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) := by
    simp only [θ,successorInstance,nextEmbedding,originRoundSubst,j,v,liftNext,varNext]
  obtain ⟨base⟩ := baseRule paid E vertices ctx ty seed
  obtain ⟨step⟩ := stepRule (body := body) (Γ := θ :: Δ.map weaken) paid E v
    (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have every := Derivation.universalElimination (emb fuel)
    (natInduction θ (by rw [inst]; exact base) (by rw [next]; exact step))
  rw [inst] at every
  obtain ⟨guard⟩ := applyAt E fuel vertices ctx ty seed out ⟨every⟩ ⟨Derivation.conjunctionLeft given⟩
  obtain ⟨result⟩ := atMember vertices seed out k guard (Derivation.conjunctionRight given)
  exact ⟨Derivation.implicationIntroduction result⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedOriginInductionProof
