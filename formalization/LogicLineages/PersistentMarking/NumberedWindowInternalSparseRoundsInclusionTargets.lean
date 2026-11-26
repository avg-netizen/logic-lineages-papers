module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundsInclusionTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseDirectedFilter (passGraph)
open NumberedWindowInternalSparseDirectedRounds (members membersTape)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)

/-- Occurrence in the output of a directed pass gives an occurrence of
the same candidate in the original vertices on that very tape. -/
def PassIncluded (E : Program 4) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (out vertices seen ctx ty k : OTerm α),
    Nonempty (Derivation body Γ ((passGraph E out vertices seen ctx ty ⊓ memberGraph out k).imp
      (memberGraph vertices k)))

def RoundsIncluded (E : Program 4) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (out fuel vertices ctx ty seed k : OTerm α),
    Nonempty (Derivation body Γ ((roundGraph E out fuel vertices ctx ty seed ⊓ memberGraph out k).imp
      (memberGraph vertices k)))

def MembersIncluded (E : Program 4) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (out vertices ctx ty seed k : OTerm α),
    Nonempty (Derivation body Γ
      ((programGraph (members E) out (membersTape vertices ctx ty seed) ⊓ memberGraph out k).imp
        (memberGraph vertices k)))

/-- Both filters are explicit: the literal zero edge at the base and the
actual E in the successor case. Membership is recovered at the original
vertices both at any genuine open fuel and at the genuine chosen length. -/
def ExactRoundsInclusionFromPass : Prop :=
  ∀ E : Program 4, PassIncluded (constantZero 4) → PassIncluded E →
    RoundsIncluded E ∧ MembersIncluded E

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundsInclusionTargets
