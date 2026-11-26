module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedBoundMotiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundReachChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowMotiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedBoundInductionProof
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
open NumberedWindowInternalSparseSeedBoundMotiveProof
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseRoundReachChecks (exact_SeedRoundZero exact_AdjacentRoundPersistence)
open NumberedWindowInternalSparseSeedBoundTargets

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem tapeRename {β : Type} (fuel vertices ctx ty seed : OTerm α) (j : α → β) :
    (fun i => (roundsTape fuel vertices ctx ty seed i).relabel j) =
      roundsTape (fuel.relabel j) (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) := by
  funext i
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun c =>
    Fin.cases ?_ (fun d => Fin.cases ?_ (fun e => Fin.elim0 e) d) c) b) a) i <;> rfl

private theorem baseRule (E : Program 4) (vertices ctx ty seed : OTerm α)
    (guard : Nonempty (Derivation body Γ (memberGraph vertices seed))) :
    Nonempty (Derivation body Γ (seedAt E z vertices ctx ty seed)) := by
  apply introduce
  intro β j Δ out keep r
  have g := renameInto guard j Δ keep
  rw [graphRename] at g
  rw [zRelabel] at r
  obtain ⟨g⟩ := g
  obtain ⟨r⟩ := r
  obtain ⟨rule⟩ := exact_SeedRoundZero E body β Δ out (vertices.relabel j) (ctx.relabel j)
    (ty.relabel j) (seed.relabel j)
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionLeft (Derivation.implicationElimination rule r)) g⟩

private theorem succAt (E : Program 4) (out fuel vertices ctx ty seed : OTerm α)
    (old : Nonempty (Derivation body Γ (seedAt E fuel vertices ctx ty seed)))
    (run : Nonempty (Derivation body Γ (roundGraph E out (suc fuel) vertices ctx ty seed))) :
    Nonempty (Derivation body Γ (memberGraph out seed)) := by
  apply programCases (rounds E) (roundsTape fuel vertices ctx ty seed) _
  intro β j Δ before keep prior
  rw [graphRename]
  rw [tapeRename] at prior
  have ih := renameInto old j Δ keep
  rw [seedAtRename] at ih
  obtain ⟨yes⟩ := applyAt E _ _ _ _ _ before ih prior
  have current := renameInto run j Δ keep
  rw [roundRename,sucRelabel] at current
  obtain ⟨current⟩ := current
  obtain ⟨prior⟩ := prior
  obtain ⟨persist⟩ := exact_AdjacentRoundPersistence E body β Δ before (out.relabel j) (fuel.relabel j)
    (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) (seed.relabel j)
  exact ⟨Derivation.implicationElimination persist
    (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction prior current) yes)⟩

private theorem stepRule (E : Program 4)
    (fuel vertices ctx ty seed : OTerm α) (old : Nonempty (Derivation body Γ (seedAt E fuel vertices ctx ty seed))) :
    Nonempty (Derivation body Γ (seedAt E (suc fuel) vertices ctx ty seed)) := by
  apply introduce
  intro β j Δ out keep r
  have prior := renameInto old j Δ keep
  rw [seedAtRename] at prior
  rw [sucRelabel] at r
  exact succAt E out _ _ _ _ _ prior r

theorem seedRounds : ExactSeedEveryRound := by
  intro E body α Γ out fuel vertices ctx ty seed
  let A := roundGraph E out fuel vertices ctx ty seed ⊓ memberGraph vertices seed
  let Δ := A :: Γ
  have given : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  let j : α → α ⊕ Fin 1 := Sum.inl
  let v : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let θ := seedAt E v (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j)
  have inst (n : OTerm α) : instantiate θ (emb n) = seedAt E n vertices ctx ty seed := by
    simp only [θ,instantiate,bindEmbedding,seedAtSubst,j,v,liftBind,varBind]
  have next : successorInstance θ = seedAt E (suc v) (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) := by
    simp only [θ,successorInstance,nextEmbedding,seedAtSubst,j,v,liftNext,varNext]
  obtain ⟨base⟩ := baseRule E vertices ctx ty seed ⟨Derivation.conjunctionRight given⟩
  obtain ⟨step⟩ := stepRule (body := body) (Γ := θ :: Δ.map weaken) E v
    (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have every := Derivation.universalElimination (emb fuel)
    (natInduction θ (by rw [inst]; exact base) (by rw [next]; exact step))
  rw [inst] at every
  obtain ⟨guard⟩ := applyAt E fuel vertices ctx ty seed out ⟨every⟩ ⟨Derivation.conjunctionLeft given⟩
  exact ⟨Derivation.implicationIntroduction guard⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedBoundInductionProof
