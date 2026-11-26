module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowSingletonProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowInductionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb z suc zRelabel sucRelabel bindEmbedding nextEmbedding liftBind varBind)
open ID1Completion.InternalTagArithmeticSupportProof (natInduction)
open ID1Completion.InternalAdditionLawsProof (liftNext varNext)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseDirectedRounds (rounds roundsTape)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparseOpenRoundsChecks (exact_OpenRoundZero exact_OpenRoundSuccessor)
open NumberedWindowInternalSparsePassWindowTargets (allWindow windowAt)
open NumberedWindowInternalSparsePassWindowChecks (exact_RoundEdgeWindows exact_PassWindowFromRetained)
open NumberedWindowInternalSparsePassWindowSyntaxProof (allRename windowRename)
open NumberedWindowInternalSparseRoundWindowMotiveProof
open NumberedWindowInternalSparseRoundWindowSingletonProof (singletonWindow)
open NumberedWindowInternalSparseRoundWindowTargets

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem tapeRename {β : Type} (fuel vertices ctx ty seed : OTerm α) (j : α → β) :
    (fun i => (roundsTape fuel vertices ctx ty seed i).relabel j) =
      roundsTape (fuel.relabel j) (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) := by
  funext i
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun c =>
    Fin.cases ?_ (fun d => Fin.cases ?_ (fun e => Fin.elim0 e) d) c) b) a) i <;> rfl

private theorem zeroAt (retained : ExactRetainedPredecessor) (X : Program 2) (W : Program 3)
    (out vertices ctx ty seed : OTerm α)
    (guard : Nonempty (Derivation body Γ (windowAt W ctx ty seed)))
    (run : Nonempty (Derivation body Γ (roundGraph (edge4 X W) out z vertices ctx ty seed))) :
    Nonempty (Derivation body Γ (allWindow W ctx ty out)) := by
  apply programCases consCode ![seed,z] _
  intro β j Δ singleton keep hs
  rw [allRename]
  rw [binaryInputsRename,zRelabel] at hs
  have start := renameInto guard j Δ keep
  rw [windowRename] at start
  obtain ⟨guarded⟩ := singletonWindow W (ctx.relabel j) (ty.relabel j) singleton (seed.relabel j) hs start
  obtain ⟨stage⟩ := exact_OpenRoundZero (edge4 X W) body β Δ (out.relabel j) (vertices.relabel j)
    (ctx.relabel j) (ty.relabel j) (seed.relabel j) singleton
  have round := renameInto run j Δ keep
  rw [roundRename,zRelabel] at round
  obtain ⟨round⟩ := round
  obtain ⟨hs⟩ := hs
  have pass := Derivation.implicationElimination (Derivation.conjunctionLeft
    (Derivation.implicationElimination stage hs)) round
  obtain ⟨preserve⟩ := exact_PassWindowFromRetained retained (constantZero 4) W
    (exact_RoundEdgeWindows X W).1 body β Δ (ctx.relabel j) (ty.relabel j) (vertices.relabel j) singleton (out.relabel j)
  exact ⟨Derivation.implicationElimination preserve (Derivation.conjunctionIntroduction guarded pass)⟩

private theorem succAt (retained : ExactRetainedPredecessor) (X : Program 2) (W : Program 3)
    (out fuel vertices ctx ty seed : OTerm α)
    (old : Nonempty (Derivation body Γ (safe X W fuel vertices ctx ty seed)))
    (run : Nonempty (Derivation body Γ (roundGraph (edge4 X W) out (suc fuel) vertices ctx ty seed))) :
    Nonempty (Derivation body Γ (allWindow W ctx ty out)) := by
  apply programCases (rounds (edge4 X W)) (roundsTape fuel vertices ctx ty seed) _
  intro β j Δ previous keep prior
  rw [allRename]
  rw [tapeRename] at prior
  have hypothesis := renameInto old j Δ keep
  rw [safeRename] at hypothesis
  obtain ⟨guarded⟩ := applyAt X W _ _ _ _ _ previous hypothesis prior
  have round := renameInto run j Δ keep
  rw [roundRename,sucRelabel] at round
  obtain ⟨stage⟩ := exact_OpenRoundSuccessor (edge4 X W) body β Δ (out.relabel j) (fuel.relabel j) (vertices.relabel j)
    (ctx.relabel j) (ty.relabel j) (seed.relabel j) previous
  obtain ⟨round⟩ := round
  obtain ⟨prior⟩ := prior
  have pass := Derivation.implicationElimination (Derivation.conjunctionLeft
    (Derivation.implicationElimination stage prior)) round
  obtain ⟨preserve⟩ := exact_PassWindowFromRetained retained (edge4 X W) W (exact_RoundEdgeWindows X W).2
    body β Δ (ctx.relabel j) (ty.relabel j) (vertices.relabel j) previous (out.relabel j)
  exact ⟨Derivation.implicationElimination preserve (Derivation.conjunctionIntroduction guarded pass)⟩

private theorem baseRule (retained : ExactRetainedPredecessor) (X : Program 2) (W : Program 3)
    (vertices ctx ty seed : OTerm α) (guard : Nonempty (Derivation body Γ (windowAt W ctx ty seed))) :
    Nonempty (Derivation body Γ (safe X W z vertices ctx ty seed)) := by
  apply introduce
  intro β j Δ out keep r
  have g := renameInto guard j Δ keep
  rw [windowRename] at g
  rw [zRelabel] at r
  exact zeroAt retained X W out _ _ _ _ g r

private theorem stepRule (retained : ExactRetainedPredecessor) (X : Program 2) (W : Program 3)
    (fuel vertices ctx ty seed : OTerm α) (old : Nonempty (Derivation body Γ (safe X W fuel vertices ctx ty seed))) :
    Nonempty (Derivation body Γ (safe X W (suc fuel) vertices ctx ty seed)) := by
  apply introduce
  intro β j Δ out keep r
  have prior := renameInto old j Δ keep
  rw [safeRename] at prior
  rw [sucRelabel] at r
  exact succAt retained X W out _ _ _ _ _ prior r

theorem roundsWindow : ExactRoundsWindowFromRetained := by
  intro retained X W body α Γ ctx ty vertices seed fuel out
  let E := edge4 X W
  let A := windowAt W ctx ty seed ⊓ roundGraph E out fuel vertices ctx ty seed
  let Δ := A :: Γ
  have given : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  let j : α → α ⊕ Fin 1 := Sum.inl
  let v : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let θ := safe X W v (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j)
  have inst (n : OTerm α) : instantiate θ (emb n) = safe X W n vertices ctx ty seed := by
    simp only [θ,instantiate,bindEmbedding,safeSubst,j,v,liftBind,varBind]
  have next : successorInstance θ = safe X W (suc v) (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) := by
    simp only [θ,successorInstance,nextEmbedding,safeSubst,j,v,liftNext,varNext]
  obtain ⟨base⟩ := baseRule retained X W vertices ctx ty seed ⟨Derivation.conjunctionLeft given⟩
  obtain ⟨step⟩ := stepRule (body := body) (Γ := θ :: Δ.map weaken) retained X W v
    (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have every := Derivation.universalElimination (emb fuel)
    (natInduction θ (by rw [inst]; exact base) (by rw [next]; exact step))
  rw [inst] at every
  obtain ⟨guard⟩ := applyAt X W fuel vertices ctx ty seed out ⟨every⟩ ⟨Derivation.conjunctionRight given⟩
  exact ⟨Derivation.implicationIntroduction guard⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowInductionProof
