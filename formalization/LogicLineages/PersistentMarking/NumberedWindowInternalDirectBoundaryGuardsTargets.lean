module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectBoundaryGuardsTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch conjunction constantZero)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalDirectSourcePartitionRawTargets
open NumberedWindowFieldAlgorithm (unpack)

def normalizeScalar (scalar : Program 1) : Program 1 := conjunction scalar (constantOne 1)
def scalarFailures (scalar : Program 1) : Program 1 :=
  .composition scratchMember ![ID1Completion.InternalListMap.map (k := 0) (normalizeScalar scalar),constantZero 1]

/-- No new list loop: find zero on the actual ordered map of normalized
calls, then invert just that failure bit. -/
def typedScratch (scalar : Program 1) : Program 1 :=
  branch (scalarFailures scalar) (constantOne 1) (constantZero 1)

def presentScratch : Program 1 := branch (.projection 0) (constantZero 1) (constantOne 1)
def atSlot (p : Program 1) (i : Fin 3) : Program 3 := .composition p ![.projection i]

/-- Decoded input order is source, target, removed. The third test is on
the actual removed scratch code, not the parser success tag. -/
def boundaryScratch (scalar : Program 1) : Program 3 :=
  conjunction (atSlot (typedScratch scalar) 0)
    (conjunction (atSlot (typedScratch scalar) 1) (atSlot presentScratch 2))

def boundaryRaw (scalar : Program 1) : Program 3 := rawSourceCheck (boundaryScratch scalar)

def ScalarFit (scalar : Program 1) (accepts : Nat → Bool) : Prop :=
  ∀ q : Nat, evaluate scalar (q ::ᵥ nil) = (accepts q).toNat

def expected (accepts : Nat → Bool) (src dst removed : Nat) : Bool :=
  match unpack src, unpack dst, unpack removed with
  | some s, some t, some r => s.all accepts && t.all accepts && !r.isEmpty
  | _,_,_ => false

def ExactNumericRawGuards : Prop := ∀ (scalar : Program 1) (accepts : Nat → Bool),
  ScalarFit scalar accepts → ∀ src dst removed,
    evaluate (boundaryRaw scalar) (src ::ᵥ dst ::ᵥ removed ::ᵥ nil) =
      (expected accepts src dst removed).toNat

structure BoundaryReports (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (src dst removed ds dt dr head tail : OTerm α) (scalar : Program 1) : Prop where
  parsed : ParsedTriplet B Γ src dst removed ds dt dr
  sourceTyped : Nonempty (Derivation B Γ (unary (typedScratch scalar) (suc z) ds))
  targetTyped : Nonempty (Derivation B Γ (unary (typedScratch scalar) (suc z) dt))
  removedCons : Nonempty (Derivation B Γ (consGraph dr head tail))

/-- Both scalar-fold reports and the actual removed cons come from one
accepted guard at the same physical raw tapes. No typing reflection into
an unrelated object graph or assumption on an old whole checker. -/
def ExactOpenRawGuards : Prop :=
  ∀ (scalar : Program 1) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (src dst removed : OTerm α) (goal : Formula α),
    Nonempty (Derivation B Γ (programGraph (boundaryRaw scalar) (suc z) (sourceTape src dst removed))) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (ds dt dr head tail : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      BoundaryReports B Δ (src.relabel j) (dst.relabel j) (removed.relabel j) ds dt dr head tail scalar →
      Nonempty (Derivation B Δ (goal.relabel j))) →
    Nonempty (Derivation B Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectBoundaryGuardsTargets
