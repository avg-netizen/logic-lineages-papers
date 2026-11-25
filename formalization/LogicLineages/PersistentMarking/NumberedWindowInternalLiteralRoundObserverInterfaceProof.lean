module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRoundLeastTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRoundObserverTargets
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)

def observe {α : Type} (O : Program 3) (ctx ty q out : OTerm α) : Formula α :=
  programGraph O out ![ctx,ty,q]

/-- An observer is stable only if the original object calculus
can move its actual reported value across each genuine edge. -/
def Preserves (E : Program 4) (O : Program 3) : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty a b out : OTerm α),
    Nonempty (Derivation B Γ (acceptEdge E ctx ty a b)) →
    Nonempty (Derivation B Γ (observe O ctx ty a out)) →
    Nonempty (Derivation B Γ (observe O ctx ty b out))

def inputs {α : Type} (E : Program 4) (O : Program 3)
    (i vertices ctx ty seed out k m : OTerm α) : Formula α :=
  observe O ctx ty seed m ⊓ (roundGraph E out i vertices ctx ty seed ⊓ memberGraph out k)

#print axioms observe
#print axioms Preserves
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRoundObserverTargets
