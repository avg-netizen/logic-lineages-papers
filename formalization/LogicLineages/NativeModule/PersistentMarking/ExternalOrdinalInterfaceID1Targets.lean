module

public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourcePresentationDefinitions
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalIDStages
public import Mathlib.SetTheory.Ordinal.Rank

@[expose] public section

/-! # External inputs of `thm:upper` (proposal for Opus B), beside `ExternalOrdinalInterfaceTargets`

- E4 `NormTheorem`: Pohlers's norm theorem (Defs 6.3.1, 6.3.5, 9.1.2; Lemma 6.5.2; Thms 9.5.5–9.5.6)
  in the form `thm:upper` applies it: every `Derivation`-provable atom `I(n)` of a positive body has
  a stage below `BH` of that body's operator. `BH` is an abstract `Ordinal.{0}`.
- R1 `InternalAccessibility`: `lem:arithmetic-accessibility`'s conclusion at one presentation, the
  uniform all-terms sentence (Opus B round-3 table, R1). Internal, not external.
Stages are `NumberedWindowExternalIDStages.stage` over `Ordinal.{0}`. -/

namespace LogicLineages.PersistentMarking.ExternalOrdinalInterfaceID1Targets
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.SourcePresentation
open NumberedWindowExternalIDOperators NumberedWindowExternalIDStages

/-- The operator of a positive body: `P ↦ {n | φ(P, n)}`. -/
def bodyOperator (B : Positive (Fin 1)) : Operator := fun P n => realize P B.formula ![n]

/-- E4: ID₁-provable positive atoms have inductive norm below `BH`. -/
def NormTheorem (BH : Ordinal.{0}) : Prop :=
  ∀ (B : Positive (Fin 1)) (n : Nat),
    Nonempty (Derivation B [] (Positive.predicate (α := Empty) (numeral n)).formula) →
    ∃ a < BH, stage (· < ·) Ordinal.lt_wf (bodyOperator B) a n

/-- R1: the all-terms sentence of the presentation `d` at context `context` is ID₁-derivable
(`d := NumberedWindowInternalPresentationTargets.data pI pJ pR pD` with the #563 programs). -/
def InternalAccessibility (d : Data) (context : Nat) : Prop :=
  Nonempty (Derivation (sourceBody d context) [] (allTermsFormula d context))

end LogicLineages.PersistentMarking.ExternalOrdinalInterfaceID1Targets
