module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRootDispatchOpenProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunRootTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunRootChecks
import LogicLineages.PersistentMarking.NumberedWindowConcreteRulePrograms
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureLogicProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRootTypedRawProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowRootDispatchAlgorithm (fixed)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax ActualPackedWindow)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualRawCalibration)
open NumberedWindowInternalSparseRawTickTargets (ActualRoot ActualFallback)
open NumberedWindowInternalSparseRawRunRootTargets (rootWitnessTerm)
open NumberedWindowInternalSparseTypedRawChecks (exact_TypedRaw5Calibration exact_OpenTypedRaw5)
open NumberedWindowInternalSparseRawRunRootChecks (exact_OpenRootOwnRun)
open NumberedWindowInternalLiteralRootDispatchNumericProof
  (LeafFit shapes guard root exact_ConcreteLiteralRoot)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit exact_OpenLiteralRootCaseElimination)

attribute [local irreducible] programGraph

/-- The eight-way root and the original physical typed raw callback can
be chosen together with unchanged context and endpoint checks. Each
branch's original numerical acceptance remains exact. -/
theorem exact_ConcreteLiteralRootRaw5 (xs : Entries) (s : Settings)
    (other window : Program 3) (syntaxCheck : Program 1)
    (fallback : ActualFallback other) (syntaxFit : ActualRawSyntax syntaxCheck)
    (windowFit : ActualPackedWindow s window) :
    ∃ leaf : Nat → Program 3, LeafFit (fixed xs s.window.2) leaf ∧
      ActualRoot (NumberedWindowConcreteCheckers.root xs s) (root leaf) ∧
      ActualRawCalibration xs s (typedRaw5 (root leaf) other window syntaxCheck) := by
  obtain ⟨leaves,fit,physical⟩ := exact_ConcreteLiteralRoot (fixed xs s.window.2)
    (NumberedWindowConcreteRulePrograms.primitive xs s.window.2)
  exact ⟨leaves,fit,physical,exact_TypedRaw5Calibration xs s (root leaves) other window syntaxCheck
    physical fallback syntaxFit windowFit⟩

/-- Opening an actual typed raw step at a literal root wrapper produces
one of the eight true guards and that physical leaf on the same raw
source, unwrapped payload, and target. Context, type, and both endpoint
checks are kept by the original typed raw parser. -/
theorem exact_OpenLiteralTypedRootCases (leaf : Nat → Program 3)
    (other window : Program 3) (syntaxCheck : Program 1)
    {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (ctx ty q payload r : OTerm α) (goal : Formula α)
    (held : D B Γ (programGraph (typedRaw5 (root leaf) other window syntaxCheck)
      (suc z) ![ctx,ty,q,rootWitnessTerm payload,r]))
    (next : ∀ tag arity, (tag,arity) ∈ shapes →
      ∀ Δ : List (Formula α), (∀ f ∈ Γ, f ∈ Δ) →
      D B Δ (bit (guard tag arity) ![q,payload,r]) →
      D B Δ (bit (leaf tag) ![q,payload,r]) → D B Δ goal) : D B Γ goal := by
  obtain ⟨codec⟩ := exact_OpenTypedRaw5 B (root leaf) other window syntaxCheck α Γ
    ctx ty q (rootWitnessTerm payload) r
  obtain ⟨h⟩ := held
  have checks := Derivation.implicationElimination (Derivation.conjunctionLeft codec) h
  have own := Derivation.conjunctionRight (Derivation.conjunctionLeft checks)
  obtain ⟨run⟩ := exact_OpenRootOwnRun B (root leaf) other α q payload r
  have selected := closedApply ⟨Derivation.conjunctionRight run⟩ ⟨own⟩
  exact exact_OpenLiteralRootCaseElimination leaf ![q,payload,r] goal selected next

#print axioms exact_ConcreteLiteralRootRaw5
#print axioms exact_OpenLiteralTypedRootCases
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRootTypedRawProof
