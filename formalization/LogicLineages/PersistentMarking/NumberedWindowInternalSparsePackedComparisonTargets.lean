module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMembersComparisonTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumEdgeTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedComparisonTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity (included)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparsePackedLeast (membersAtSeed)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)
open ID1Completion.InternalLessThan (strictLess)

/-- These witnesses belong to the three actual physical programs at a single seed. -/
def resultAt {α : Type} (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx ty seed vertices pool minimum : OTerm α) : Formula α :=
  unary (scratchVertices C s) vertices seed ⊓
    (programGraph (membersAtSeed C X W s) pool ![ctx,ty,seed] ⊓ leastGraph C X W s ctx ty seed minimum)

def coversSeed {α : Type} (va vb b seedA : OTerm α) : Formula α :=
  included va vb ⊓ memberGraph b seedA

def ExactSelectedInSuppliedPool : Prop :=
  ∀ (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty seed pool minimum : OTerm α),
    Nonempty (Derivation body Γ ((programGraph (membersAtSeed C X W s) pool ![ctx,ty,seed] ⊓
      leastGraph C X W s ctx ty seed minimum).imp (memberGraph pool minimum)))

def ExactPackedSeedOrder : Prop :=
  ExactRetainedPredecessor → ∀ (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty seedA seedB va vb a b x y : OTerm α),
    let runs := resultAt C X W s ctx ty seedA va a x ⊓ resultAt C X W s ctx ty seedB vb b y
    Nonempty (Derivation body Γ ((runs ⊓ coversSeed va vb b seedA).imp (strictLess x y).not))

def ExactMutualPackedSeedEquality : Prop :=
  ExactRetainedPredecessor → ∀ (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty seedA seedB va vb a b x y : OTerm α),
    let runs := resultAt C X W s ctx ty seedA va a x ⊓ resultAt C X W s ctx ty seedB vb b y
    Nonempty (Derivation body Γ ((runs ⊓ (coversSeed va vb b seedA ⊓ coversSeed vb va a seedB)).imp (eqn x y)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedComparisonTargets
