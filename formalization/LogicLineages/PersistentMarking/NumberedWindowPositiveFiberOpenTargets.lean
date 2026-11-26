module
public import LogicLineages.PersistentMarking.NumberedWindowPositiveFiberPrograms

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowPositiveFiberOpenTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowPositiveFiberPrograms

/-- Literal arity-three output-one graph, the same formula as the existing
source arithmetic acceptance predicate, without importing term computability. -/
abbrev one {α : Type} (r : Program 3) (q w v : OTerm α) : Formula α :=
  programGraph r (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm) ![q,w,v]

/-- Both actual unary arithmetic graph calls have a single object-level value.
There is no standard-natural evaluation or reflection principle here. -/
def shared {α : Type} (a : Program 1) (q v : OTerm α) : Formula α :=
  let value : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  existsOne (programGraph a value ![q.relabel Sum.inl] ⊓
    programGraph a value ![v.relabel Sum.inl])

def OpenSharedTest : Prop :=
  ∀ (a : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (q w v : OTerm α),
    Nonempty (Derivation body Γ (one (agree a) q w v)) ↔
    Nonempty (Derivation body Γ (shared a q v))

/-- The selected checker unpacks and repacks in the original finitary calculus
on arbitrary free terms, with the very same supplied certificate and both
actual endpoint graph witnesses. -/
def OpenFiberRules : Prop :=
  ∀ (ctx ty : Program 1) (r : Program 3) (body : Positive (Fin 1))
    (α : Type) (Γ : List (Formula α)) (q w v : OTerm α),
    Nonempty (Derivation body Γ (one (guarded ctx ty r) q w v)) ↔
      Nonempty (Derivation body Γ (shared ctx q v)) ∧
      Nonempty (Derivation body Γ (shared ty q v)) ∧
      Nonempty (Derivation body Γ (one r q w v))

end LogicLineages.PersistentMarking.NumberedWindowPositiveFiberOpenTargets
