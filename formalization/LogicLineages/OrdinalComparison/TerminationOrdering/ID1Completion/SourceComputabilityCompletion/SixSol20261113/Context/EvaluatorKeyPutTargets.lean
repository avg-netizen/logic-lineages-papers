module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyPutDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyPutTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorKeyPut
/-- Full retained native/preparation contracts at this explicitly NEW tuple.
E is NOT required to equal the original numeric representative; the actual
bounded minimum must retain that original all-vector calibration. -/
def ActualRetention : Prop :=
 ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
 (H G : Program 1) (W : Program 2) (P : Program 3),
 GlobalSourcePackage.InputsCalibrated n arity p →
 OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
 OriginalVariableLeaves.ContextGuardCalibrated n G →
 OriginalUniverseDecoder.HeadWindowCalibrated n arity W →
 OriginalTransparentMinimum.ClassTestCalibrated n arity P →
 OriginalMixedPrepared.Properties n arity (SixSol20261113.Erasure.PutIntegration.seed p H G W) H G W P ∧
 (OriginalTransparentMinimum.ClassTestCalibrated n arity (classTest p H G W P) ∧
 (GlobalSourcePackage.InputsCalibrated n arity (prepared p H G W) ∧
 (GlobalSourcePackage.InputsCalibrated n arity (minimumInputs p H G W P) ∧
 (GlobalSourcePackage.InputsCalibrated n arity (refined p H G W P) ∧
 (OriginalTransparentMinimum.Properties n arity (prepared p H G W) H G W (classTest p H G W P) ∧
 OriginalFinalGuardedRank.Properties n arity (minimumInputs p H G W P) H G W)))))

/-- Separate INTERNAL actual minimum-hit law. No calibration premise, native
reflection, desired E equality, or candidate admission is supplied. -/
def ActualHit : Prop := ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (seed candidate parameter : OTerm alpha),
 Nonempty (Derivation body Delta (Domain p H G W seed parameter)) →
 Nonempty (Derivation body Delta (graph3 (relationTest p H G W P) (numeral 1) seed candidate parameter)) →
 Nonempty (Derivation body Delta (Domain p H G W candidate parameter ⊓ Same p H G W seed candidate parameter))

/-- Separate INTERNAL equality of literal candidate rows under one common E
output and both actual domain admissions. No candidate key/output equality
or equality of class-test rows is a premise. -/
def ActualRows : Prop := ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (left right candidate parameter : OTerm alpha),
 Nonempty (Derivation body Delta (Domain p H G W left parameter)) →
 Nonempty (Derivation body Delta (Domain p H G W right parameter)) →
 Nonempty (Derivation body Delta (Same p H G W left right parameter)) →
 Nonempty (Derivation body Delta
   ((graph3 (relationTest p H G W P) (numeral 1) left candidate parameter).iff
    (graph3 (relationTest p H G W P) (numeral 1) right candidate parameter)))

def ActualFinalPutStep : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (s t cert parameter typ raw head base label : OTerm alpha),
  Nonempty (Derivation body Delta
    ((Fields p H G W P s t cert parameter typ raw head base label).imp
      (stepAccepted (finalData p H G W P) (finalInputs p H G W P).oldStep
        s t cert parameter)))


/-- Full original positive certificate at the NEW final tuple, never the old witness. -/
def ActualFinalPutObjectCertificate : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha)) (context : Nat)
    (s t cert parameter typ raw head base label gamma x y quotient entry path first second : OTerm alpha),
  Nonempty (Derivation body Delta
    ((Fields p H G W P s t cert parameter typ raw head base label ⊓
      ((graph1 (finalInputs p H G W P).window (numeral 1) (numeral context) ⊓
        graph2 InternalPairing.pairing parameter (numeral context) gamma) ⊓
      ((InternalParameterizedCanonicalResultFold.foldGraph (finalData p H G W P) x s parameter ⊓
        InternalParameterizedCanonicalResultFold.foldGraph (finalData p H G W P) y t parameter) ⊓
      ((graph3 edgeCode quotient s t cert ⊓
        (graph2 InternalPairing.pairing entry y quotient ⊓
          graph2 InternalListCodec.consCode path entry (numeral 0))) ⊓
        (graph2 InternalPairing.pairing first gamma x ⊓ graph2 InternalPairing.pairing second gamma y))))).imp
      (InternalAccessibilityRules.certificate (GlobalSourcePackage.source (finalInputs p H G W P))
        false context first second path)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyPutTargets
