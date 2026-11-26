module
public import LogicLineages.PersistentMarking.NumberedWindowConcreteFormulaTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAccessibilityTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalAccessibilityRules ID1Completion.SourcePresentation
open NumberedWindowPresentationCheckers NumberedWindowFormulaCalibrationTargets
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)

/-- The object-calculus rules for the scalar and multiset slices of this data. -/
structure Rules (p : Data) : Prop where
  equation : ∀ odd context α (x : OrdinaryArithmetic.Term α),
    Nonempty (Derivation (sourceBody p context) []
      ((membership odd x).iff (carrier p odd context x ⊓ successors p odd context x)))
  carrierOfMembership : ∀ odd context α (Γ : List (Formula α)) (x : OrdinaryArithmetic.Term α),
    Nonempty (Derivation (sourceBody p context) Γ (membership odd x)) →
    Nonempty (Derivation (sourceBody p context) Γ (carrier p odd context x))
  successor : ∀ odd context α (Γ : List (Formula α)) (x y : OrdinaryArithmetic.Term α),
    Nonempty (Derivation (sourceBody p context) Γ (membership odd x)) →
    Nonempty (Derivation (sourceBody p context) Γ (edge p odd context x y)) →
    Nonempty (Derivation (sourceBody p context) Γ (membership odd y))
  certified : ∀ odd context α (Γ : List (Formula α)) (x y w : OrdinaryArithmetic.Term α),
    Nonempty (Derivation (sourceBody p context) Γ (membership odd x)) →
    Nonempty (Derivation (sourceBody p context) Γ (certificate p odd context x y w)) →
    Nonempty (Derivation (sourceBody p context) Γ (membership odd y))
  introduction : ∀ odd context α (Γ : List (Formula α)) (x : OrdinaryArithmetic.Term α),
    Nonempty (Derivation (sourceBody p context) Γ (carrier p odd context x)) →
    Nonempty (Derivation (sourceBody p context) Γ (successors p odd context x)) →
    Nonempty (Derivation (sourceBody p context) Γ (membership odd x))

def ConcreteInternalAccessibility : Prop := ∀ (xs : Entries) (s : Settings),
  ∃ (i j : Program 1) (r d : Program 3), Evaluates (checks xs s) i j r d ∧
    Interprets (checks xs s) (data i j r d) ∧ Rules (data i j r d)

end LogicLineages.PersistentMarking.NumberedWindowInternalAccessibilityTargets
