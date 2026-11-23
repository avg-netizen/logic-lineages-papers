module
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinMembersClosureTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredThinEdgeReversalTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedSeedPresenceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalThinGuardedEdgeCoverProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedSeedPresenceChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredThinEdgeReversalProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinPackedEdgeMutualSeedProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue headTransport)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseDirectedRounds (members membersTape)
open NumberedWindowInternalSparsePackedLeast (membersAtSeed poolAtSeed)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparsePackedSeedPresenceChecks (exact_SeedInGivenVertices exact_SeedInGivenPool)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (pairedExchange)
open NumberedWindowInternalMeasuredThinEdgeReversalProof (exact_PairedEdgeReversal)
open NumberedWindowInternalThinGuardedEdgeCoverProof (exact_ThinGuardedEdgeCover)
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)
open NumberedWindowInternalThinRoundExhaustionTargets (CountLengthBound)
open NumberedWindowInternalThinUncoveredCountTargets (InternalStrictDecrease)
open NumberedWindowInternalThinMembersClosureTargets (ExactMembersEdgeClosure)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenActualMembersFromCover (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx ty seed vertices pool : OTerm α)
    (cover : Nonempty (Derivation B Γ (unary (scratchVertices C s) vertices seed)))
    (packed : Nonempty (Derivation B Γ (programGraph (membersAtSeed C X W s) pool ![ctx,ty,seed]))) :
    Nonempty (Derivation B Γ (programGraph (members (edge4 X W)) pool
      (membersTape vertices ctx ty seed))) := by
  let xs : Fin 3 → OTerm α := ![ctx,ty,seed]
  apply compositionRecover (members (edge4 X W))
    ![poolAtSeed C s,.projection 0,.projection 1,.projection 2]
    pool xs (membersTape vertices ctx ty seed) packed
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => ?_) k) j) i
  · apply compositionValue (scratchVertices C s) (fun _ : Fin 1 => .projection 2)
      vertices xs ![seed] cover
    intro k
    obtain rfl := Fin.eq_zero k
    exact projectionValue 2 xs
  · exact projectionValue 0 xs
  · exact projectionValue 1 xs
  · obtain rfl := Fin.eq_zero l
    exact projectionValue 2 xs

/-- With the genuine members-closure law, real guarded paired physical
edges yield cross-seed occurrence in both actual original pools.
The same cover is recovered from the actual guard, never from a
numeric promise or equality of the two raw representatives. -/
theorem exact_OpenThinPairedMutualSeedPresence
    (close : ExactMembersEdgeClosure) (bound : CountLengthBound) (pred : ExactRetainedPredecessor)
    (strict : InternalStrictDecrease) (C : Program 3) (base : Program 2) (W : Program 3) (s : Settings)
    (ctx ty a b va vb pa pb x y : OTerm α) :
    let X := guardedExchange C s (pairedExchange base)
    Derivation B Γ (leastGraph C X W s ctx ty a x) →
    Derivation B Γ (leastGraph C X W s ctx ty b y) →
    Derivation B Γ (unary (scratchVertices C s) va a) →
    Derivation B Γ (unary (scratchVertices C s) vb b) →
    Derivation B Γ (programGraph (membersAtSeed C X W s) pa ![ctx,ty,a]) →
    Derivation B Γ (programGraph (membersAtSeed C X W s) pb ![ctx,ty,b]) →
    Derivation B Γ (acceptEdge (edge4 X W) ctx ty a b) →
    Nonempty (Derivation B Γ (memberGraph pb a ⊓ memberGraph pa b)) := by
  intro X leastA leastB coverA coverB packedA packedB edge
  obtain ⟨same⟩ := exact_ThinGuardedEdgeCover C s (pairedExchange base) W B α Γ ctx ty a b va vb
  have eq := Derivation.implicationElimination same (Derivation.conjunctionIntroduction edge
    (Derivation.conjunctionIntroduction coverA coverB))
  obtain ⟨opposite⟩ := exact_PairedEdgeReversal C s base W B α Γ ctx ty a b
  have reverse := Derivation.implicationElimination opposite edge
  obtain ⟨inVA⟩ := exact_SeedInGivenVertices C X W s B α Γ ctx ty a x va
  obtain ⟨inVB⟩ := exact_SeedInGivenVertices C X W s B α Γ ctx ty b y vb
  have hasVA := Derivation.implicationElimination inVA (Derivation.conjunctionIntroduction leastA coverA)
  have hasVB := Derivation.implicationElimination inVB (Derivation.conjunctionIntroduction leastB coverB)
  obtain ⟨aThere⟩ := headTransport scratchMember (suc z) va vb ![a] ⟨eq⟩ ⟨hasVA⟩
  obtain ⟨bThere⟩ := headTransport scratchMember (suc z) vb va ![b] ⟨symm eq⟩ ⟨hasVB⟩
  obtain ⟨inPA⟩ := exact_SeedInGivenPool C X W s B α Γ ctx ty a x pa
  obtain ⟨inPB⟩ := exact_SeedInGivenPool C X W s B α Γ ctx ty b y pb
  have hasPA := Derivation.implicationElimination inPA (Derivation.conjunctionIntroduction leastA packedA)
  have hasPB := Derivation.implicationElimination inPB (Derivation.conjunctionIntroduction leastB packedB)
  obtain ⟨mA⟩ := exact_OpenActualMembersFromCover C X W s ctx ty a va pa ⟨coverA⟩ ⟨packedA⟩
  obtain ⟨mB⟩ := exact_OpenActualMembersFromCover C X W s ctx ty b vb pb ⟨coverB⟩ ⟨packedB⟩
  obtain ⟨forward⟩ := close bound pred strict (edge4 X W) B α Γ va ctx ty a pa a b
  obtain ⟨backward⟩ := close bound pred strict (edge4 X W) B α Γ vb ctx ty b pb b a
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationElimination backward (Derivation.conjunctionIntroduction mB
      (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction hasPB reverse) aThere)))
    (Derivation.implicationElimination forward (Derivation.conjunctionIntroduction mA
      (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction hasPA edge) bThere)))⟩

#print axioms exact_OpenActualMembersFromCover
#print axioms exact_OpenThinPairedMutualSeedPresence
end LogicLineages.PersistentMarking.NumberedWindowInternalThinPackedEdgeMutualSeedProof
