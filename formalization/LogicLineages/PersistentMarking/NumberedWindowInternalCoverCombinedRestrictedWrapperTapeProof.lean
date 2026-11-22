module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrapperTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrapperTapeProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparsePackedLeast (poolAtSeed)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverCombinedRestrictedWrapperTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem rawValueOnMatchingTape (F : Program 1) (ctx ty raw out : OTerm α)
    (actual : Nonempty (Derivation body Γ (unary F out raw))) :
    Nonempty (Derivation body Γ
      (programGraph (.composition F (fun _ : Fin 1 => .projection 2)) out ![ctx,ty,raw])) := by
  apply compositionValue F (fun _ : Fin 1 => .projection 2) out ![ctx,ty,raw] ![raw] actual
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 2 ![ctx,ty,raw]

theorem ownSeedOnSameMatchingTape (C : Program 3) (s : Settings) (ctx ty raw vertices : OTerm α)
    (cover : Nonempty (Derivation body Γ (unary (scratchVertices C s) vertices raw)))
    (hit : Nonempty (Derivation body Γ (memberGraph vertices raw))) :
    Nonempty (Derivation body Γ (windowAt (thinOwnSeed C s) ctx ty raw)) := by
  apply compositionValue scratchMember ![poolAtSeed C s,.projection 2] (suc z)
    ![ctx,ty,raw] ![vertices,raw] hit
  intro i
  exact Fin.cases (rawValueOnMatchingTape (scratchVertices C s) ctx ty raw vertices cover)
    (Fin.cases (projectionValue 2 ![ctx,ty,raw]) (fun j => Fin.elim0 j)) i

theorem memberOfOwnSeedOnSameMatchingTape (C : Program 3) (s : Settings) (ctx ty raw vertices : OTerm α)
    (cover : Nonempty (Derivation body Γ (unary (scratchVertices C s) vertices raw)))
    (own : Nonempty (Derivation body Γ (windowAt (thinOwnSeed C s) ctx ty raw))) :
    Nonempty (Derivation body Γ (memberGraph vertices raw)) := by
  apply compositionRecover scratchMember ![poolAtSeed C s,.projection 2] (suc z)
    ![ctx,ty,raw] ![vertices,raw] own
  intro i
  exact Fin.cases (rawValueOnMatchingTape (scratchVertices C s) ctx ty raw vertices cover)
    (Fin.cases (projectionValue 2 ![ctx,ty,raw]) (fun j => Fin.elim0 j)) i

#print axioms rawValueOnMatchingTape
#print axioms ownSeedOnSameMatchingTape
#print axioms memberOfOwnSeedOnSameMatchingTape

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrapperTapeProof
