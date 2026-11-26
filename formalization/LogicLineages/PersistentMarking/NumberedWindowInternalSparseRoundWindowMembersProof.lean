module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowInductionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowMembersProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (programRename projectionValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePassWindowTargets (windowAt allWindow)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename allRename)
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparsePackedLeast (poolAtSeed membersAtSeed)
open NumberedWindowInternalSparseDirectedRounds (members membersTape poolLength)
open NumberedWindowInternalSparseOpenRoundsChecks (exact_OpenMembersAtLength)
open NumberedWindowInternalSparseRoundWindowTargets
open NumberedWindowInternalSparseRoundWindowInductionProof (roundsWindow)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename quadInputsRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem atLength (paid : ExactRetainedPredecessor) (X : Program 2) (W : Program 3)
    (ctx ty vertices seed out : OTerm α)
    (guard : Nonempty (Derivation body Γ (windowAt W ctx ty seed)))
    (selected : Nonempty (Derivation body Γ (programGraph (members (edge4 X W)) out
      (membersTape vertices ctx ty seed)))) :
    Nonempty (Derivation body Γ (allWindow W ctx ty out)) := by
  apply programCases poolLength ![vertices] _
  intro β j Δ fuel keep len
  rw [allRename]
  rw [unaryInputsRename] at len
  have g := renameInto guard j Δ keep
  rw [windowRename] at g
  have ss := renameInto selected j Δ keep
  simp only [programRename,membersTape,quadInputsRename] at ss
  obtain ⟨atLen⟩ := exact_OpenMembersAtLength (edge4 X W) body β Δ (out.relabel j) fuel
    (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j)
  obtain ⟨rule⟩ := roundsWindow paid X W body β Δ (ctx.relabel j) (ty.relabel j)
    (vertices.relabel j) (seed.relabel j) fuel (out.relabel j)
  obtain ⟨l⟩ := len
  obtain ⟨v⟩ := ss
  obtain ⟨g⟩ := g
  have run := Derivation.implicationElimination
    (Derivation.conjunctionLeft (Derivation.implicationElimination atLen l)) v
  exact ⟨Derivation.implicationElimination rule (Derivation.conjunctionIntroduction g run)⟩

private theorem takePool (paid : ExactRetainedPredecessor) (C : Program 3) (X : Program 2)
    (W : Program 3) (s : Settings) (ctx ty seed out : OTerm α)
    (guard : Nonempty (Derivation body Γ (windowAt W ctx ty seed)))
    (computed : Nonempty (Derivation body Γ (programGraph (membersAtSeed C X W s) out ![ctx,ty,seed]))) :
    Nonempty (Derivation body Γ (allWindow W ctx ty out)) := by
  apply programCases (poolAtSeed C s) ![ctx,ty,seed] _
  intro β j Δ vertices keep vv
  rw [allRename]
  rw [tripleInputsRename] at vv
  have g := renameInto guard j Δ keep
  rw [windowRename] at g
  have ss := renameInto computed j Δ keep
  rw [programRename,tripleInputsRename] at ss
  let xs : Fin 3 → OTerm β := ![ctx.relabel j,ty.relabel j,seed.relabel j]
  apply atLength paid X W (ctx.relabel j) (ty.relabel j) vertices (seed.relabel j) (out.relabel j) g
  apply compositionRecover (members (edge4 X W)) ![poolAtSeed C s,.projection 0,.projection 1,.projection 2]
    (out.relabel j) xs (membersTape vertices (ctx.relabel j) (ty.relabel j) (seed.relabel j)) ss
  intro k
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun c => ?_) b) a) k
  · exact vv
  · exact projectionValue 0 xs
  · exact projectionValue 1 xs
  · obtain rfl := Fin.eq_zero c
    exact projectionValue 2 xs

theorem chosenWindow : ExactChosenMembersWindowFromRetained := by
  intro paid C X W s body α Γ ctx ty seed out
  let A := windowAt W ctx ty seed ⊓ programGraph (membersAtSeed C X W s) out ![ctx,ty,seed]
  have h : Derivation body (A :: Γ) A := Derivation.hypothesis List.mem_cons_self
  obtain ⟨d⟩ := takePool paid C X W s ctx ty seed out
    ⟨Derivation.conjunctionLeft h⟩ ⟨Derivation.conjunctionRight h⟩
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowMembersProof
