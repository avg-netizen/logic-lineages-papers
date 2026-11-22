module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedComparisonTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedComparisonSelectionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMembersComparisonChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedBoundChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InclusionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMembersClosureChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedComparisonChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename compositionValue projectionValue)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseDirectedRounds (members membersTape)
open NumberedWindowInternalSparsePackedLeast (poolAtSeed membersAtSeed)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseRoundsInclusionTargets (MembersIncluded)
open NumberedWindowInternalSparseCoverOccurrenceTargets
open NumberedWindowInternalSparseCoverOccurrenceSyntaxProof (coverIntro coverRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)

open NumberedWindowInternalSparseDirectedSeen (acceptEdge edgeTape)
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)
open NumberedWindowInternalSparseMembersClosureChecks (exact_MembersEdgeClosure)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalSparseMinimumEdgeTargets
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open NumberedWindowInternalSparsePackedComparisonTargets
open NumberedWindowInternalSparseMembersComparisonTargets (membersGraph)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalQuotientComparisonProof (compareView actualOriginalComparison)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.SourceComputabilityCompletion.Continuation20261114
attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem poolArgs (C : Program 3) (s : Settings) (xs : Fin 3 → OTerm α)
    (vertices : OTerm α) (hv : Nonempty (Derivation body Γ (unary (scratchVertices C s) vertices (xs 2))))
    (k : Fin 4) :
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


theorem exact_SelectedInSuppliedPool : ExactSelectedInSuppliedPool :=
  NumberedWindowInternalSparsePackedComparisonSelectionProof.selected

private theorem computed (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx ty seed v pool minimum : OTerm α) (d : Derivation body Γ (resultAt C X W s ctx ty seed v pool minimum)) :
    Nonempty (Derivation body Γ (membersGraph (edge4 X W) pool v ctx ty seed)) := by
  let xs := ![ctx,ty,seed]
  exact compositionRecover (members (edge4 X W)) ![poolAtSeed C s,.projection 0,.projection 1,.projection 2]
    pool xs (membersTape v ctx ty seed) ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight d)⟩
    (poolArgs C s xs v ⟨Derivation.conjunctionLeft d⟩)

theorem exact_PackedSeedOrder : ExactPackedSeedOrder := by
  intro pred C X W s body α Γ ctx ty seedA seedB va vb a b x y
  let runs := resultAt C X W s ctx ty seedA va a x ⊓ resultAt C X W s ctx ty seedB vb b y
  let Δ := (runs ⊓ coversSeed va vb b seedA) :: Γ
  have h : Derivation body Δ (runs ⊓ coversSeed va vb b seedA) := Derivation.hypothesis List.mem_cons_self
  have small := Derivation.conjunctionLeft (Derivation.conjunctionLeft h)
  have large := Derivation.conjunctionRight (Derivation.conjunctionLeft h)
  obtain ⟨sa⟩ := computed C X W s ctx ty seedA va a x small
  obtain ⟨sb⟩ := computed C X W s ctx ty seedB vb b y large
  obtain ⟨mono⟩ := NumberedWindowInternalSparseMembersComparisonChecks.exact_MembersSeedInclusion
    pred (edge4 X W) body α Δ va vb ctx ty seedA seedB a b
  have inc := Derivation.implicationElimination mono (Derivation.conjunctionIntroduction
    (Derivation.conjunctionRight h) (Derivation.conjunctionIntroduction sa sb))
  obtain ⟨selected⟩ := exact_SelectedInSuppliedPool C X W s body α Δ ctx ty seedA a x
  have hit := Derivation.implicationElimination selected (Derivation.conjunctionRight small)
  obtain ⟨other⟩ := PrimaryMonotonicity.InclusionProof.eliminate a b x ⟨inc⟩ ⟨hit⟩
  obtain ⟨bound⟩ := NumberedWindowInternalSparsePackedBoundChecks.exact_OpenPackedLeastLowerBound
    C X W s body α Δ ctx ty seedB b x y
  have result := Derivation.conjunctionRight large
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination bound
    (Derivation.conjunctionIntroduction (Derivation.conjunctionRight result)
      (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft result) other)))⟩

private theorem unorderedEqual (x y : OTerm α) (left : Derivation body Γ (ltF x y).not)
    (right : Derivation body Γ (ltF y x).not) : Nonempty (Derivation body Γ (eqn x y)) := by
  obtain ⟨comparison⟩ := actualOriginalComparison body α x y
  have split := compareView (weakenClosed comparison Γ)
  let L := ltF x y
  let R := ltF y x
  let M := eqn x y
  have noLeft : Derivation body Γ (L.imp M) := Derivation.implicationIntroduction
    (Derivation.explosion (Derivation.implicationElimination (addHyp left L) (Derivation.hypothesis List.mem_cons_self)))
  have noRight : Derivation body Γ (R.imp M) := Derivation.implicationIntroduction
    (Derivation.explosion (Derivation.implicationElimination (addHyp right R) (Derivation.hypothesis List.mem_cons_self)))
  have same : Derivation body Γ (M.imp M) := Derivation.implicationIntroduction
    (Derivation.hypothesis List.mem_cons_self)
  exact ⟨disjunctionElimination split noLeft (Derivation.implicationIntroduction
    (disjunctionElimination (Derivation.hypothesis List.mem_cons_self)
      (addHyp same (M ⊔ R)) (addHyp noRight (M ⊔ R))))⟩

theorem exact_MutualPackedSeedEquality : ExactMutualPackedSeedEquality := by
  intro pred C X W s body α Γ ctx ty seedA seedB va vb a b x y
  let runs := resultAt C X W s ctx ty seedA va a x ⊓ resultAt C X W s ctx ty seedB vb b y
  let conditions := coversSeed va vb b seedA ⊓ coversSeed vb va a seedB
  let Δ := (runs ⊓ conditions) :: Γ
  have h : Derivation body Δ (runs ⊓ conditions) := Derivation.hypothesis List.mem_cons_self
  have lr := Derivation.conjunctionLeft h
  have both := Derivation.conjunctionRight h
  obtain ⟨left⟩ := exact_PackedSeedOrder pred C X W s body α Δ ctx ty seedA seedB va vb a b x y
  obtain ⟨right⟩ := exact_PackedSeedOrder pred C X W s body α Δ ctx ty seedB seedA vb va b a y x
  have leftBound := Derivation.implicationElimination left (Derivation.conjunctionIntroduction lr (Derivation.conjunctionLeft both))
  have swapped := Derivation.conjunctionIntroduction (Derivation.conjunctionRight lr) (Derivation.conjunctionLeft lr)
  have rightBound := Derivation.implicationElimination right (Derivation.conjunctionIntroduction swapped (Derivation.conjunctionRight both))
  obtain ⟨same⟩ := unorderedEqual x y leftBound rightBound
  exact ⟨Derivation.implicationIntroduction same⟩

#print axioms exact_SelectedInSuppliedPool
#print axioms exact_PackedSeedOrder
#print axioms exact_MutualPackedSeedEquality
end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedComparisonChecks
