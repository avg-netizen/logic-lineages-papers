module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationRepresentativeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedComparisonChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationRepresentativeProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (programRename compositionValue projectionValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparsePackedLeast (poolAtSeed)
open NumberedWindowInternalSparseDirectedRounds (members membersTape poolLength)
open NumberedWindowInternalSparseOpenRoundsChecks (exact_OpenMembersAtLength)
open NumberedWindowInternalSparsePackedComparisonChecks (exact_SelectedInSuppliedPool)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationSyntaxProof (motiveRename stepRename)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationProof (exact_RoundApplicationLeastAt)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationTargets
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationRepresentativeTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)}

/-- Re-derived from the private `poolArgs` of #835's checks. -/
private theorem poolArgs {α : Type} {Γ : List (Formula α)} (C : Program 3) (s : Settings)
    (xs : Fin 3 → OTerm α) (vertices : OTerm α)
    (hv : Nonempty (Derivation body Γ (unary (scratchVertices C s) vertices (xs 2)))) (k : Fin 4) :
    Nonempty (Derivation body Γ (programGraph
      ((![poolAtSeed C s,.projection 0,.projection 1,.projection 2] : Fin 4 → Program 3) k)
      (membersTape vertices (xs 0) (xs 1) (xs 2) k) xs)) := by
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun c => ?_) b) a) k
  · apply compositionValue (scratchVertices C s) (fun _ : Fin 1 => .projection 2)
      vertices xs ![xs 2] hv
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 2 xs
  · exact projectionValue 0 xs
  · exact projectionValue 1 xs
  · obtain rfl := Fin.eq_zero c
    exact projectionValue 2 xs

theorem exact_LeastRepresentativeApplication : ExactLeastRepresentativeApplication := by
  intro Cf Xf Wf sf N C X W s body α Γ fctx fty f x ctx ty dom cod arg μ m step mf lx
  -- the seed's physical cover
  apply programCases (scratchVertices Cf sf) ![f] _
  intro β j Δ vertices keep physical
  rw [motiveRename]
  rw [NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof.inputsRename] at physical
  replace physical : Nonempty (Derivation body Δ (unary (scratchVertices Cf sf) vertices (f.relabel j))) :=
    physical
  have step1 := stepRename N C X W s (edge4 Xf Wf) fctx fty ctx ty dom cod arg μ m step j Δ keep
  have mf1 := renameInto mf j Δ keep
  rw [motiveRename] at mf1
  have lx1 := renameInto lx j Δ keep
  rw [leastRename] at lx1
  -- the computed members pool
  apply programCases (members (edge4 Xf Wf))
    (membersTape vertices (fctx.relabel j) (fty.relabel j) (f.relabel j)) _
  intro γ i Θ pool keep2 computed
  rw [motiveRename]
  simp only [membersTape,quadInputsRename] at computed
  have v := renameInto physical i Θ keep2
  rw [NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof.unaryRename] at v
  have lx2 := renameInto lx1 i Θ keep2
  rw [leastRename] at lx2
  have step2 := stepRename N C X W s (edge4 Xf Wf) _ _ _ _ _ _ _ _ _ step1 i Θ keep2
  have mf2 := renameInto mf1 i Θ keep2
  rw [motiveRename] at mf2
  let xs : Fin 3 → OTerm γ := ![(fctx.relabel j).relabel i,(fty.relabel j).relabel i,(f.relabel j).relabel i]
  let ys := membersTape (vertices.relabel i) ((fctx.relabel j).relabel i) ((fty.relabel j).relabel i)
    ((f.relabel j).relabel i)
  obtain ⟨run⟩ := compositionValue (members (edge4 Xf Wf))
    ![poolAtSeed Cf sf,.projection 0,.projection 1,.projection 2] pool xs ys computed
    (poolArgs Cf sf xs (vertices.relabel i) v)
  obtain ⟨selection⟩ := exact_SelectedInSuppliedPool Cf Xf Wf sf body γ Θ ((fctx.relabel j).relabel i)
    ((fty.relabel j).relabel i) ((f.relabel j).relabel i) pool ((x.relabel j).relabel i)
  obtain ⟨lx2⟩ := lx2
  have hit := Derivation.implicationElimination selection (Derivation.conjunctionIntroduction run lx2)
  -- the round at the pool's length
  apply programCases poolLength ![vertices.relabel i] _
  intro δ k Ξ fuel keep3 length
  rw [motiveRename]
  rw [NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof.inputsRename] at length
  have computed3 := renameInto computed k Ξ keep3
  simp only [programRename,membersTape,quadInputsRename] at computed3
  have hit3 := renameInto ⟨hit⟩ k Ξ keep3
  rw [graphRename] at hit3
  have step3 := stepRename N C X W s (edge4 Xf Wf) _ _ _ _ _ _ _ _ _ step2 k Ξ keep3
  have mf3 := renameInto mf2 k Ξ keep3
  rw [motiveRename] at mf3
  obtain ⟨atLen⟩ := exact_OpenMembersAtLength (edge4 Xf Wf) body δ Ξ (pool.relabel k) fuel
    ((vertices.relabel i).relabel k) (((fctx.relabel j).relabel i).relabel k)
    (((fty.relabel j).relabel i).relabel k) (((f.relabel j).relabel i).relabel k)
  obtain ⟨l⟩ := length
  obtain ⟨c3⟩ := computed3
  have round := Derivation.implicationElimination
    (Derivation.conjunctionLeft (Derivation.implicationElimination atLen l)) c3
  exact exact_RoundApplicationLeastAt (edge4 Xf Wf) N C X W s body δ Ξ fuel _ _ _ _ (pool.relabel k)
    _ _ _ _ _ _ _ _ step3 mf3 ⟨round⟩ hit3

#print axioms exact_LeastRepresentativeApplication
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationRepresentativeProof
