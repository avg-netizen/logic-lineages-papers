module
public import LogicLineages.PersistentMarking.NumberedWindowPresentationClauses
public import LogicLineages.PersistentMarking.NumberedWindowInternalPresentationTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowFormulaCalibrationTargets
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.SourcePresentation PositiveArithmeticOperators
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowPresentationClauses

def Evaluates (f : Checks) (i j : Program 1) (r d : Program 3) : Prop :=
  (∀ x, evaluate i (x ::ᵥ nil) = (f.scalar x).toNat) ∧
  (∀ x, evaluate j (x ::ᵥ nil) = (f.multiset x).toNat) ∧
  (∀ x c y, evaluate r (x ::ᵥ c ::ᵥ y ::ᵥ nil) = (f.positive x c y).toNat) ∧
  (∀ x c y, evaluate d (x ::ᵥ c ::ᵥ y ::ᵥ nil) = (f.direct x c y).toNat)

def Interprets (f : Checks) (p : Data) : Prop :=
  ∀ context (P : Nat → Prop),
    (∀ z, realize P (sourceBody p context).formula ![z] ↔ tagged f P z) ∧
    (realize P (allTermsFormula p context) Empty.elim ↔ terms f P)

def InterpretsEvaluatingPrograms : Prop :=
  ∀ (f : Checks) i j r d, Evaluates f i j r d → Interprets f (data i j r d)
end LogicLineages.PersistentMarking.NumberedWindowFormulaCalibrationTargets
