module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open OriginalFunctionNeutrality UniformCertificateCompletion OriginalVariableObject
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Literal full-output equality on all original raw input/parameter pairs,
including inactive, malformed and nonclosed-window inputs. -/
def ActualOriginalFunctionNeutralityRefinementEquality : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data) (window : Program 1),
  InternalOriginalUniformDescentSelection.Calibrated n arity data →
  Path.windowCalibrated n window →
  (∀ v : List.Vector Nat 2,
    evaluate (representative data window) v = evaluate data.oldRepresentative v) ∧
  InternalOriginalUniformDescentSelection.Calibrated n arity (baseData data window)

def ActualOriginalFunctionNeutralitySelectedPreservation : Prop :=
  ∀ (data : Data) (window : Program 1),
  SelectedMarkPreservation (selectedData data window) window

def ActualOriginalFunctionNeutralityFullFoldPreservation : Prop :=
  ∀ (data : Data) (window : Program 1),
  FullFoldMarkPreservation (selectedData data window) window

/-- Two valid raw sources with one common actual canonical output have the
same original function-level neutrality test at every symbolic value. -/
def ActualOriginalFunctionNeutralityCanonicalComparison : Prop :=
  ∀ (data : Data) (window : Program 1)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out left right leftType rightType parameter value : OTerm alpha),
  let selected := selectedData data window
  Nonempty (Derivation body Delta
    ((windowGraph window left parameter ⊓
      (windowGraph window right parameter ⊓
        (InternalParameterizedCanonicalResultFold.sourcePremises selected left leftType parameter ⊓
          (InternalParameterizedCanonicalResultFold.sourcePremises selected right rightType parameter ⊓
            (InternalParameterizedCanonicalResultFold.foldGraph selected out left parameter ⊓
              InternalParameterizedCanonicalResultFold.foldGraph selected out right parameter))))).imp
      ((markGraph value left).iff (markGraph value right))))

/-- One original tuple is refined before every window and context. Its SAME
final source supplies the full Package, original root fields, function-level
neutrality reflection and all previously established neutral/variable laws. -/
def ActualOriginalFunctionNeutralityGlobalSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ p : GlobalSourcePackage.Inputs,
    GlobalSourcePackage.InputsCalibrated n arity p ∧
    (let r := finalInputs p
     GlobalSourcePackage.InputsCalibrated n arity r ∧
     GlobalSourcePackage.Package n arity
       (GlobalSourcePackage.source r) (GlobalSourcePackage.computability r)
       (GlobalSourcePackage.lift r) ∧
     OriginalConstructorShape.FullFoldRootFields (OuterSelection.data r.base r.window) r.window ∧
     FullFoldMarkPreservation (OuterSelection.data r.base r.window) r.window ∧
     OriginalNeutralLeaf.NeutralBottom (OriginalNeutralLeaf.endpoint r) r.window r.oldStep ∧
     ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
       SubtypeClosed (fun tau => tau ∈ S) →
       let context := OrdinaryArithmeticQuotient.contextCode symbols S table
       VariableCertificateBottom (GlobalSourcePackage.source r)
         (GlobalSourcePackage.computability r) context ∧
       VariableLeast (GlobalSourcePackage.source r)
         (GlobalSourcePackage.computability r) context)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityTargets
