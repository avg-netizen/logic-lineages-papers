module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedLengthReachTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedLengthReachLocalProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedLengthReachPackedProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseDirectedRounds (members membersTape)
open NumberedWindowInternalSparsePackedLeast (poolAtSeed)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalCoverCombinedRestrictedLengthReachLocalProof (exact_OpenCoverLengthReach)
open NumberedWindowInternalCoverCombinedRestrictedLengthReachTargets

attribute [local irreducible] programGraph

private theorem poolArgs {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (C : Program 3) (s : Settings) (xs : Fin 3 → OTerm α)
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

theorem exact_OpenCoverPackedLengthReach : ExactOpenCoverPackedLengthReach := by
  intro C X W s body α Γ ctx ty vertices a b fuel pool scratch length ma mb edge packed
  let xs : Fin 3 → OTerm α := ![ctx,ty,a]
  have selected := compositionRecover (members (edge4 X W))
    ![poolAtSeed C s,.projection 0,.projection 1,.projection 2] pool xs (membersTape vertices ctx ty a)
    packed (poolArgs C s xs vertices scratch)
  exact exact_OpenCoverLengthReach (edge4 X W) body α Γ ctx ty vertices a b fuel pool length ma mb edge selected

#print axioms exact_OpenCoverPackedLengthReach
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedLengthReachPackedProof
