module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeCheckerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeCheckerTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalQuotientEdgeChecker
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- One actual triple of Program witnesses works on every natural input for
each original fixed window, context and precedence table. -/
def ActualOriginalProgramsExist : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
  ∃ data : Data, Calibrated n arity symbols S Gamma table data

/-- Equality to the unchanged numericEdgeTest on ALL inputs, including
failed decodes and finite windows which are not subtype closed. -/
def ActualOriginalCheckerCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (data : Data),
  Calibrated n arity symbols S Gamma table data →
  ∀ v : List.Vector Nat 3,
    evaluate (checker data) v =
      (NumberedNumericQuotientEdge.numericEdgeTest n arity symbols S Gamma table
        (v.get 0) (v.get 1) (v.get 2)).toNat

/-- Internal decomposition and reconstruction at actual certificate
selector outputs. There is no calibration premise in this graph law. -/
def ActualOriginalAcceptanceEquation : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (α : Type)
    (x y certificate rawSource rawTarget rawStep : OTerm α),
  Nonempty (Derivation body []
    ((selectors certificate rawSource rawTarget rawStep).imp
      ((accepted data x y certificate).iff
        (requirements data x y rawSource rawTarget rawStep))))

/-- Once the actual representative values are supplied, acceptance is
exactly original step acceptance together with the two endpoint equations. -/
def ActualOriginalAcceptanceAtValues : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (α : Type)
    (x y certificate rawSource rawTarget rawStep sourceValue targetValue : OTerm α),
  Nonempty (Derivation body []
    ((valuePremises data certificate rawSource rawTarget rawStep sourceValue targetValue).imp
      ((accepted data x y certificate).iff
        (valueRequirements data x y rawSource rawTarget rawStep sourceValue targetValue))))

/-- The same exact rule for a certificate supplied by the original pair
constructor. Its field graphs are derived internally, not assumed separately. -/
def ActualOriginalEncodedAcceptanceEquation : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (α : Type)
    (x y certificate rawSource rawTarget rawStep : OTerm α),
  Nonempty (Derivation body []
    ((graph3 edgeCode certificate rawSource rawTarget rawStep).imp
      ((accepted data x y certificate).iff
        (requirements data x y rawSource rawTarget rawStep))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeCheckerTargets
