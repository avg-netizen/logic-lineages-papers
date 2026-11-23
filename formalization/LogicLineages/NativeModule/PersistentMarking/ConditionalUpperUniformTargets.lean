module

public import LogicLineages.NativeModule.PersistentMarking.ConditionalMain16Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesDefinitions

/-! Conditional `thm:upper` / `thm:main` with the uniform internal hypothesis (Opus B, round 5;
not a twin).

The internal hypothesis is the all-terms derivability statement of the internal ID₁ line,
`Nonempty (Derivation (sourceBody d c) [] (allTermsFormula d c))` (Opus A's
`ExternalOrdinalInterfaceID1Targets.InternalAccessibility d c`; PENDING in the ID1Completion
targets `ActualSourceInternalAccessibility` / `ActualContextUniformInternalAccessibility`),
taken at programs that evaluate the original four checks of the window (the presentation of
#571).  Three steps reduce it to the individual atoms of `ConditionalUpperTargets.IndividualAccessibility`. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.ConditionalUpperUniformTargets
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators PositiveArithmeticTransforms SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.SourcePresentation ID1Completion.InternalAccessibilityRules
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowExternalIDOperators NumberedWindowFormulaCalibrationTargets NumberedWindowPresentationCheckers
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowArithmeticAllContextTargets (AdmittedAddress)
open ExternalOrdinalInterfaceTargets ConditionalTowerCofinality

universe u

/-- (i) ∀-elimination of the all-terms sentence at a numeral: carrier instance implies membership. -/
def AllTermsInstance : Prop :=
  ∀ (B : Positive (Fin 1)) (d : Data) (c x : Nat),
    Nonempty (Derivation B [] (allTermsFormula d c)) →
      Nonempty (Derivation B [] ((carrier (α := Empty) d false c (numeral x)).imp (membership false (numeral x))))

/-- (ii) Internal truth of the scalar checker's graph at numerals where it evaluates to 1. -/
def ScalarCarrierNumeralTruth : Prop :=
  ∀ (B : Positive (Fin 1)) (d : Data) (c x : Nat),
    evaluate d.scalar (c ::ᵥ x ::ᵥ List.Vector.nil) = 1 →
      Nonempty (Derivation B [] (carrier (α := Empty) d false c (numeral x)))

/-- (iii) The original even tag of a numeral is provably the numeral of its double. -/
def EvenTagNumeral : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (x : Nat),
    Nonempty (Derivation B [] (arithmeticEmbedding.onFormula
      ((tagTerm false (numeral x : OrdinaryArithmetic.Term α)).equal (numeral (2 * x)))))

/-- Bridge: at programs evaluating the window's original checks, the uniform sentence gives the
individual I-atom (as a numeral) of every admitted scalar address. -/
def UniformToIndividual : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty), DecisionSourceUniverse.Closed K →
    ∀ (i j : Program 1) (r d : Program 3) (c : Nat),
      Evaluates (checks S.entries (fixed S K)) i j r d →
      ExternalOrdinalInterfaceID1Targets.InternalAccessibility (data i j r d) c →
      ∀ x, AdmittedAddress S K x →
        Nonempty (Derivation (sourceBody (data i j r d) c) []
          (Positive.predicate (α := Empty) (numeral (tagScalar x))).formula)

/-- The uniform internal hypothesis: for each closed window, the all-terms sentence is
ID₁-derivable at some programs evaluating the original checks and some outer context. -/
def UniformAccessibility : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty), DecisionSourceUniverse.Closed K →
    ∃ (i j : Program 1) (r d : Program 3) (c : Nat),
      Evaluates (checks S.entries (fixed S K)) i j r d ∧
      ExternalOrdinalInterfaceID1Targets.InternalAccessibility (data i j r d) c

def ConditionalUpperUniform : Prop :=
  ∀ BH : Ordinal.{0}, ExternalOrdinalInterfaceID1Targets.NormTheorem BH → UniformAccessibility →
    ConditionalUpperTargets.UpperStatement BH

def ConditionalMain16Uniform : Prop :=
  ∀ (I : Type u) [LinearOrder I] (D : CollapseData I Ordinal.{0}) (BH : Ordinal.{0}),
    ExternalOrdinalInterfaceID1Targets.NormTheorem BH → UniformAccessibility →
    Calibration D → TowerHypotheses D → BHIdentification D BH →
    ConditionalMain16Targets.Main16Statement BH

end LogicLineages.PersistentMarking.ConditionalUpperUniformTargets
