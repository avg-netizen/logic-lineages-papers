module
public import LogicLineages.PersistentMarking.NumberedWindowInternalProbeTargets
public import LogicLineages.PersistentMarking.NumberedWindowTypedProbeProgramTargets
@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open NumberedWindowInternalProbeTargets (OTerm freshAt)
open NumberedWindowScalarAlgorithm (Settings)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

/-- The actual graph output zero encodes absent; it is not a selected address. -/
def rejectedAt {α : Type} (a : Program 1) (q : OTerm α) : Formula α :=
  programGraph a OrdinaryArithmetic.zeroTerm ![q]

/-- The actual graph output is the successor of a selected address. -/
def chosenAt {α : Type} (a : Program 1) (q : OTerm α) : Formula α :=
  existsOne (freshAt a (q.relabel Sum.inl) (.var (.inr (0 : Fin 1))))

def FreshProbeOutputCases : Prop :=
  ∀ (body : Positive (Fin 1)) (a : Program 1) (α : Type)
    (Γ : List (Formula α)) (q : OTerm α),
    Nonempty (Derivation body Γ (rejectedAt a q ⊔ chosenAt a q))

def FreshProbeRejectedExcludes : Prop :=
  ∀ (body : Positive (Fin 1)) (a : Program 1) (α : Type)
    (Γ : List (Formula α)) (q u : OTerm α),
    Nonempty (Derivation body Γ ((rejectedAt a q).imp (freshAt a q u).not))

def FreshProbeUnique : Prop :=
  ∀ (body : Positive (Fin 1)) (a : Program 1) (α : Type)
    (Γ : List (Formula α)) (q u v : OTerm α),
    Nonempty (Derivation body Γ ((freshAt a q u ⊓ freshAt a q v).imp (equal u v)))

/-- Choose the actual option-code program, with its original calibration on
all raw inputs, and obtain the arbitrary-open split for that same program. -/
def ExactOriginalFreshProbeObjectCases : Prop :=
  ∀ (s : Settings) (body : Positive (Fin 1)),
    ∃ a : Program 1,
      (∀ n, evaluate a (n ::ᵥ nil) = Encodable.encode (NumberedWindowTypedProbe.probe s n)) ∧
      ∀ (α : Type) (Γ : List (Formula α)) (q : OTerm α),
        Nonempty (Derivation body Γ (rejectedAt a q ⊔ chosenAt a q))

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeTargets
