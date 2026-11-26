module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPackedLeastOnProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemoRoundApplicationMotiveProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalLiteralPackedLeastOnProof (leastOnGraph)

/-- A literal auxiliary application with one of its two operands
supplied by a moving class representative. No raw reduction is
asserted in the argument position. -/
def varyAuxiliary {α : Type} (varyArgument : Bool) (dom cod k fixed : OTerm α) : OTerm α :=
  if varyArgument then auxiliaryTerm dom cod fixed k else auxiliaryTerm dom cod k fixed

/-- The application motive at a typed child-level round member `k`: `k` has the
fixed selected measure `μ` under `N`, and the application of `k` to the fixed
`arg` (annotations `dom`, `cod`) has the successful packed least `m` of the
application-level programs `C Q s` at `ctx`, `ty`. -/
def appMotive {α : Type} (N : Program 1) (C : Program 3) (Q : Program 4) (varyArgument : Bool)
    (s : Settings) (ctx ty dom cod arg μ m k : OTerm α) : Formula α :=
  unary N μ k ⊓ leastOnGraph C Q s ctx ty (varyAuxiliary varyArgument dom cod k arg) m

/-- One-edge premise in the style of `SameLeastOnEdge`, at every body, context
and term: an accepted function-level edge `w → k` of the edge program `E` at
`fctx`, `fty` carries the application motive from `w` to `k`. -/
def ApplicationEdgeStep (E : Program 4) (N : Program 1) (C : Program 3) (Q : Program 4)
    (varyArgument : Bool) (s : Settings) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (fctx fty ctx ty dom cod arg μ m w k : OTerm α),
    Nonempty (Derivation body Γ ((acceptEdge E fctx fty w k ⊓
      appMotive N C Q varyArgument s ctx ty dom cod arg μ m w).imp (appMotive N C Q varyArgument s ctx ty dom cod arg μ m k)))

/-- The same premise relative to one context `Γ` and fixed parameters: it is
asked only in contexts that extend `Γ` along a renaming, so facts held in `Γ`
(type guards, argument window) may be used to pay it. -/
def ApplicationEdgeStepAt (E : Program 4) (N : Program 1) (C : Program 3) (Q : Program 4)
    (varyArgument : Bool) (s : Settings) (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (fctx fty ctx ty dom cod arg μ m : OTerm α) : Prop :=
  ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (w k : OTerm β),
    (∀ p ∈ Γ, p.relabel j ∈ Δ) →
    Nonempty (Derivation body Δ (acceptEdge E (fctx.relabel j) (fty.relabel j) w k)) →
    Nonempty (Derivation body Δ (appMotive N C Q varyArgument s (ctx.relabel j) (ty.relabel j)
      (dom.relabel j) (cod.relabel j) (arg.relabel j) (μ.relabel j) (m.relabel j) w)) →
    Nonempty (Derivation body Δ (appMotive N C Q varyArgument s (ctx.relabel j) (ty.relabel j)
      (dom.relabel j) (cod.relabel j) (arg.relabel j) (μ.relabel j) (m.relabel j) k))

/-- Round induction with the application motive, relative premise: every member
`k` of an actual finite round (any count `i`) of the members computation for `E`
from `seed` satisfies the motive, given the motive at the seed. -/
def ExactRoundApplicationLeastAt : Prop :=
  ∀ (E : Program 4) (N : Program 1) (C : Program 3) (Q : Program 4) (varyArgument : Bool) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (i vertices fctx fty seed out k ctx ty dom cod arg μ m : OTerm α),
    ApplicationEdgeStepAt E N C Q varyArgument s body Γ fctx fty ctx ty dom cod arg μ m →
    Nonempty (Derivation body Γ (appMotive N C Q varyArgument s ctx ty dom cod arg μ m seed)) →
    Nonempty (Derivation body Γ (roundGraph E out i vertices fctx fty seed)) →
    Nonempty (Derivation body Γ (memberGraph out k)) →
    Nonempty (Derivation body Γ (appMotive N C Q varyArgument s ctx ty dom cod arg μ m k))

/-- The same in the formula style of #835 `ExactRoundLeast`, under the global
one-edge premise. -/
def ExactRoundApplicationLeast : Prop :=
  ∀ (E : Program 4) (N : Program 1) (C : Program 3) (Q : Program 4) (varyArgument : Bool) (s : Settings),
    ApplicationEdgeStep E N C Q varyArgument s →
    ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
      (i vertices fctx fty seed out k ctx ty dom cod arg μ m : OTerm α),
      Nonempty (Derivation body Γ ((appMotive N C Q varyArgument s ctx ty dom cod arg μ m seed ⊓
        (roundGraph E out i vertices fctx fty seed ⊓ memberGraph out k)).imp
        (appMotive N C Q varyArgument s ctx ty dom cod arg μ m k)))

theorem exact_AuxiliaryPositionPrograms {α : Type} (d c q fixed : OTerm α) :
    varyAuxiliary false d c q fixed = auxiliaryTerm d c q fixed ∧
    varyAuxiliary true d c q fixed = auxiliaryTerm d c fixed q :=
  ⟨rfl,rfl⟩

#print axioms exact_AuxiliaryPositionPrograms
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemoRoundApplicationMotiveProof
