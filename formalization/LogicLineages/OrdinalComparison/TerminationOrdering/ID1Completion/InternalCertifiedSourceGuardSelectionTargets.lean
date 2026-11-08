module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedSourceGuardSelectionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedSourceGuardSelectionTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalCertifiedSourceGuardSelection

/-- All-input source correspondence for the EXPLICIT strengthened Programs.
Under subtype closure, original numericStepSound supplies raw target-universe
membership on accepted steps. Actual goodRun calibration supplies H=1 on all
natural inputs. Original canonical typed acceptance and the checked N
calibration supply N(value)=value. These suppliers must be proved theorems,
not additional hypotheses or internal reflection rules. Malformed and rejected
inputs retain their original zero behavior. No bad-window claim is made. -/
def ActualOriginalCertifiedSourceGuardCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (data : Data),
  SubtypeClosed (fun tau => tau ∈ S) →
  Calibrated n arity symbols S Gamma table data →
  SelectedCalibrated n arity symbols S Gamma table data

/-- Genuine INTERNAL iff for the selected step AST. Arbitrary leaves,
positive bodies and symbolic terms are allowed; no calibration, subtype
closure, universe witness, or successful-run premise is assumed. Every
actual H and source-validity graph remains on the factorized side. -/
def ActualOriginalCertifiedStepAcceptanceFactorization : Prop :=
  ∀ (data : Data) (body : Positive (Fin 1)) (α : Type) (s t k : OTerm α),
  Nonempty (Derivation body []
    ((stepAccepted data s t k).iff (stepFactors data s t k)))

/-- Genuine INTERNAL iff for the selected canonical typed AST. It exposes
the actual H graph and the actual N fixed-point graph, not their external
evaluation equalities. Type is a symbolic original code; the input order
remains [value,type]. No canonicality or representative congruence is assumed. -/
def ActualOriginalCertifiedTypedAcceptanceFactorization : Prop :=
  ∀ (data : Data) (body : Positive (Fin 1)) (α : Type) (value typ : OTerm α),
  Nonempty (Derivation body []
    ((typedAccepted data value typ).iff (typedFactors data value typ)))

/-- ONE shared leaf selection precedes every internal positive body, variable
type and symbolic value/type/step input. The SAME literal selected ASTs are
calibrated on all natural inputs and satisfy both internal factorizations.
This fixed-context selection is restricted to subtype-closed windows; it is
not a uniform compiler, bad-window fallback, application congruence, edge/path
lift or CertifiedApplicationLift. No such assertion is a Data field/premise. -/
def ActualOriginalCertifiedSourceGuardSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun tau => tau ∈ S) →
  ∃ data : Data,
    Calibrated n arity symbols S Gamma table data ∧
      (SelectedCalibrated n arity symbols S Gamma table data ∧
        ∀ (body : Positive (Fin 1)) (α : Type),
          (∀ (s t k : OTerm α), Nonempty (Derivation body []
            ((stepAccepted data s t k).iff (stepFactors data s t k)))) ∧
          (∀ (value typ : OTerm α), Nonempty (Derivation body []
            ((typedAccepted data value typ).iff (typedFactors data value typ)))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedSourceGuardSelectionTargets
