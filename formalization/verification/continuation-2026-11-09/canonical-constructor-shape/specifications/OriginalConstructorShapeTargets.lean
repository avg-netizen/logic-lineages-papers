module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open OriginalConstructorShape UniformCertificateCompletion OriginalVariableObject
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Full-output equality on EVERY original raw input, including malformed,
inactive and nonclosed-window values; no valid-input or fixed-Gamma premise. -/
def ActualOriginalConstructorShapeRefinementEquality : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data) (window : Program 1),
  InternalOriginalUniformDescentSelection.Calibrated n arity data →
  Path.windowCalibrated n window →
  (∀ v : List.Vector Nat 2,
    evaluate (representative data window) v = evaluate data.oldRepresentative v) ∧
  InternalOriginalUniformDescentSelection.Calibrated n arity (baseData data window)

def ActualOriginalConstructorShapeSelectedPreservation : Prop :=
  ∀ (data : Data) (window : Program 1),
  SelectedMarkPreservation (selectedData data window) window

def ActualOriginalConstructorShapeFullFoldPreservation : Prop :=
  ∀ (data : Data) (window : Program 1),
  FullFoldMarkPreservation (selectedData data window) window

def ActualOriginalConstructorShapeRootFields : Prop :=
  ∀ (data : Data) (window : Program 1),
  FullFoldRootFields (selectedData data window) window

/-- Compare two raw sources at one COMMON actual final fold output and
parameter. Application/lambda shape and application domain reflect back to
the raw sources. Equality of canonical component outputs is not asserted. -/
def ActualOriginalCanonicalRootComparison : Prop :=
  ∀ (data : Data) (window : Program 1)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out left right leftType rightType parameter value domain : OTerm alpha),
  let selected := selectedData data window
  Nonempty (Derivation body Delta
    ((windowGraph window left parameter ⊓
      (windowGraph window right parameter ⊓
        (InternalParameterizedCanonicalResultFold.sourcePremises selected left leftType parameter ⊓
          (InternalParameterizedCanonicalResultFold.sourcePremises selected right rightType parameter ⊓
            (InternalParameterizedCanonicalResultFold.foldGraph selected out left parameter ⊓
              InternalParameterizedCanonicalResultFold.foldGraph selected out right parameter))))).imp
      (((tagGraph value left).iff (tagGraph value right)) ⊓
        ((applicationShape domain left).iff (applicationShape domain right)))))

/-- One original tuple and its one ordered shape/neutral/variable refinement
precede all windows. The SAME final tuple supplies calibration, full Package,
root-shape reflection, the neutral law and both existing variable Object laws. -/
def ActualOriginalConstructorShapeGlobalSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ p : GlobalSourcePackage.Inputs,
    GlobalSourcePackage.InputsCalibrated n arity p ∧
    (let r := finalInputs p
     GlobalSourcePackage.InputsCalibrated n arity r ∧
     GlobalSourcePackage.Package n arity
       (GlobalSourcePackage.source r) (GlobalSourcePackage.computability r)
       (GlobalSourcePackage.lift r) ∧
     FullFoldRootFields (OuterSelection.data r.base r.window) r.window ∧
     OriginalNeutralLeaf.NeutralBottom (OriginalNeutralLeaf.endpoint r) r.window r.oldStep ∧
     ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
       SubtypeClosed (fun tau => tau ∈ S) →
       let context := OrdinaryArithmeticQuotient.contextCode symbols S table
       VariableCertificateBottom (GlobalSourcePackage.source r)
         (GlobalSourcePackage.computability r) context ∧
       VariableLeast (GlobalSourcePackage.source r)
         (GlobalSourcePackage.computability r) context)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeTargets
