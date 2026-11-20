module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePair
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldInductionTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph ID1Completion.InternalClosedPrograms
open ID1Completion.InternalGraphComposition (OTerm)
open NumberedWindowInternalSparsePair (fieldCons)

def atCode {α : Type} (θ : Formula (α ⊕ Fin 1)) (n : OTerm α) : Formula α :=
  instantiate θ (arithmeticEmbedding.onTerm n)

def atIndex {α : Type} (θ : Formula (α ⊕ Fin 1)) (i : Fin 3) : Formula (α ⊕ Fin 3) :=
  θ.relabel (Sum.elim Sum.inl (fun _ => Sum.inr i))

def consGraph {α : Type} (n h t : OTerm α) : Formula α :=
  programGraph fieldCons n ![h,t]

def someTail {α : Type} (n h : OTerm α) : Formula α :=
  existsOne (consGraph (n.relabel Sum.inl) (h.relabel Sum.inl) (.var (.inr 0)))

def someCons {α : Type} (n : OTerm α) : Formula α :=
  existsOne (someTail (n.relabel Sum.inl) (.var (.inr 0)))

def nonzero {α : Type} (n : OTerm α) : Formula α :=
  (equal n OrdinaryArithmetic.zeroTerm).not

/-- A positive code can be unparseable at its first field; the nil case
alone does not suffice for sparse arithmetic induction. -/
def malformed {α : Type} (n : OTerm α) : Formula α :=
  nonzero n ⊓ (someCons n).not

def gapRule {α : Type} (θ : Formula (α ⊕ Fin 1)) : Formula α :=
  allOne ((malformed (.var (.inr 0))).imp θ)

def consBody {α : Type} (θ : Formula (α ⊕ Fin 1)) : Formula (α ⊕ Fin 3) :=
  (consGraph (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))).imp
    ((atIndex θ 2).imp (atIndex θ 0))

def consRule {α : Type} (θ : Formula (α ⊕ Fin 1)) : Formula α :=
  allBlock (consBody θ)

def premises {α : Type} (θ : Formula (α ⊕ Fin 1)) : Formula α :=
  atCode θ OrdinaryArithmetic.zeroTerm ⊓ (gapRule θ ⊓ consRule θ)

/-- Single actual object theorem. The invariant is any first-order formula
of the already-retained language with its one inductive predicate. -/
def SparseFieldInductionSchema : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (θ : Formula (α ⊕ Fin 1)),
    Nonempty (Derivation body [] ((premises θ).imp (allOne θ)))

/-- Contextual use with any symbolic code; all three premises remain
object formulas in the caller's original calculus and proof context. -/
def SparseFieldInductionAtCode : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (θ : Formula (α ⊕ Fin 1)) (n : OTerm α),
    Nonempty (Derivation body Γ (premises θ)) →
    Nonempty (Derivation body Γ (atCode θ n))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldInductionTargets
