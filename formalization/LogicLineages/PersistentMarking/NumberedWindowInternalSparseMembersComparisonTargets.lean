module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePrefixedRoundsTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseMembersComparisonTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity (included)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseDirectedFilter (passGraph)
open NumberedWindowInternalSparseDirectedRounds (members membersTape)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)

def membersGraph {α : Type} (E : Program 4) (pool vertices ctx ty seed : OTerm α) : Formula α :=
  programGraph (members E) pool (membersTape vertices ctx ty seed)

/-- Both the traversed vertices and the fixed seen input may grow by
membership inclusion. The two literal outputs need not be equal codes. -/
def ExactPassInputsMonotone : Prop :=
  ExactRetainedPredecessor → ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (va vb sa sb ctx ty a b : OTerm α),
    Nonempty (Derivation body Γ (((included va vb ⊓ included sa sb) ⊓
      (passGraph E a va sa ctx ty ⊓ passGraph E b vb sb ctx ty)).imp (included a b)))

/-- The physical members result is closed under every pass on a sublist in
the membership sense, with that result as the fixed seen input. -/
def ExactRestrictedMembersPrefixed : Prop :=
  ExactRetainedPredecessor → ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (va vb ctx ty seed pool later : OTerm α),
    Nonempty (Derivation body Γ (((included va vb ⊓ membersGraph E pool vb ctx ty seed) ⊓
      passGraph E later va pool ctx ty).imp (included later pool)))

/-- Distinct seeds and possibly distinct physical vertex lists, without
supplying either chosen length or an intermediate round. -/
def ExactMembersSeedInclusion : Prop :=
  ExactRetainedPredecessor → ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (va vb ctx ty seedA seedB a b : OTerm α),
    Nonempty (Derivation body Γ (((included va vb ⊓ memberGraph b seedA) ⊓
      (membersGraph E a va ctx ty seedA ⊓ membersGraph E b vb ctx ty seedB)).imp (included a b)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseMembersComparisonTargets
