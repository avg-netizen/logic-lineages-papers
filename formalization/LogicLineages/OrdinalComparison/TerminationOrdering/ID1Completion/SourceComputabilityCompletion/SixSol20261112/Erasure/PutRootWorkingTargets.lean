module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PutRootDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PutRootWorkingTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion PutRoot
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedFiniteUniverse
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Actual original PUT root test, at arbitrary label/target/replacement.
Source universe membership is tested rather than supplied as an assumption. -/
def ActualOriginalNumericPutCertificate : Prop := by
  classical
  exact ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (head : Head (Fin n))
    (base : AuxArguments (Fin n) arity Gamma (headArguments arity head))
    (label target replacement : Nat),
    let s := packedNumber (⟨headResult head,.ordinary head base⟩ : Packed (Fin n) arity Gamma)
    let t := packedNumber (⟨headResult head,.numbered label head (headResult head) base [] .nil⟩ : Packed (Fin n) arity Gamma)
    NumberedNumericStep.numericStepTest n arity symbols S Gamma table s target
      (Nat.pair 0 (Nat.pair replacement (Nat.pair 0 label))) =
        decide (InUniverse symbols S (.ordinary head base) ∧ target = t ∧ replacement = t)

/-- ALL source/certificate/parameter vectors, including malformed inputs.
Native preservation and internal graph introduction are separate obligations. -/
def ActualOriginalPutLeafEquality : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs),
  GlobalSourcePackage.InputsCalibrated n arity p →
  ∀ v : List.Vector Nat 4, evaluate (refineInputs p).oldStep v = evaluate p.oldStep v

def ActualOriginalPutCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs),
  GlobalSourcePackage.InputsCalibrated n arity p →
  GlobalSourcePackage.InputsCalibrated n arity (refineInputs p)

/-- Independent original-calculus raw PUT introduction from actual constructor
and literal result/certificate graphs; no opaque old leaf acceptance premise. -/
def ActualOriginalPutIntroduction : Prop :=
  ∀ (source : Program 2) (oldStep : Program 4) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (s t cert parameter typ raw head base label : OTerm alpha),
  Nonempty (Derivation body Delta
    ((Premises source s t cert parameter typ raw head base label).imp
      (graph4 (refined source oldStep) InternalOriginalStepGuard.one s t cert parameter)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PutRootWorkingTargets
