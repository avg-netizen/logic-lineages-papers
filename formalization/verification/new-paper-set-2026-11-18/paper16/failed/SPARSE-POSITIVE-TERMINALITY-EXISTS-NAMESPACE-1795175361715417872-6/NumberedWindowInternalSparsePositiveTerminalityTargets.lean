module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalClosedPrograms
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph loopGraph)

/-- The actual selected recursor ended at its own scratch pair with raw
cursor zero. Its encoded current remains a genuine existential object
variable; current zero (rejection) is not excluded. -/
def terminalScratch {α : Type} (out : OTerm α) : Formula α :=
  existsOne (scratchGraph (out.relabel Sum.inl) z (.var (.inr 0)))

/-- Exactly the retained arithmetic comparison certificate < S(fuel),
i.e. certificate ≤ fuel, at the original raw code, not a list length. -/
def sufficientAt {α : Type} (raw : Program 5) (least : Program 3)
    (out fuel ctx ty current certificate : OTerm α) : Formula α :=
  ((ltF certificate (suc fuel)) ⊓ loopGraph raw least out fuel ctx ty current certificate).imp
    (terminalScratch out)

/-- A single actual formula, leaving context/type fixed but quantifying
all fuel/current/output terms within the sparse-field induction motive.
The cons case can therefore use the genuinely advanced current. -/
def uniformAt {α : Type} (raw : Program 5) (least : Program 3)
    (ctx ty certificate : OTerm α) : Formula α :=
  let fuel : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let current : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let out : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  allBlock (sufficientAt raw least out fuel (ctx.relabel Sum.inl) (ty.relabel Sum.inl)
    current (certificate.relabel Sum.inl))

/-- Object-arithmetic terminality with arbitrary free input and at least
the actual raw certificate as fuel. No native evaluation premise. -/
def OpenSufficientFuelTerminal : Prop :=
  ∀ (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3) (α : Type)
    (ctx ty certificate : OTerm α),
    Nonempty (Derivation body [] (uniformAt raw least ctx ty certificate))

/-- The same true terminal shape at the exact raw-code fuel selected by
the unchanged source AST, without an added user-supplied inequality. -/
def OpenChosenFuelTerminal : Prop :=
  ∀ (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3) (α : Type)
    (out ctx ty current certificate : OTerm α),
    Nonempty (Derivation body []
      ((loopGraph raw least out certificate ctx ty current certificate).imp (terminalScratch out)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityTargets
