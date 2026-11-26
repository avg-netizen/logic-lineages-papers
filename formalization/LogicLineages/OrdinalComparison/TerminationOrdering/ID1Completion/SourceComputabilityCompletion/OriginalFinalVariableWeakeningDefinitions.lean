module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableWeakening
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors (graph1 graph2)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Only literal original constructor/pair/cons graphs. The same raw type,
outer Context, and decoder output are retained. The added context head is
unrestricted. Gamma uses the ORIGINAL Encodable list constructor. -/
def Shape {alpha : Type}
    (raw shifted variableCode shiftedVariable typ index parameter extendedParameter
      context gamma extendedGamma addedType : OTerm alpha) : Formula alpha :=
  graph1 OriginalRawSyntaxTransport.variableConstructor variableCode index ⊓
  (graph1 OriginalRawSyntaxTransport.variableConstructor shiftedVariable
      (OrdinaryArithmetic.succTerm index) ⊓
  (graph2 InternalPairing.pairing raw typ variableCode ⊓
  (graph2 InternalPairing.pairing shifted typ shiftedVariable ⊓
  (graph2 InternalPairing.pairing parameter context gamma ⊓
  (graph2 InternalListCodec.consCode extendedGamma addedType gamma ⊓
   graph2 InternalPairing.pairing extendedParameter context extendedGamma)))))

/-- Independent full-output source weakening at the IDENTICAL finalData of
one constructed variable-refined input. No successful source/window test,
native calibration, desired transport, or canonical representative is a premise. -/
def SourceLaw (guard : Program 1) (p : GlobalSourcePackage.Inputs) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out raw shifted variableCode shiftedVariable typ index parameter extendedParameter
      context gamma extendedGamma addedType : OTerm alpha),
  let D := OriginalLambdaTraversalSelection.finalData (OriginalVariableLeaves.refineInputs guard p)
  Nonempty (Derivation body Delta
    ((Shape raw shifted variableCode shiftedVariable typ index parameter extendedParameter
        context gamma extendedGamma addedType).imp
      ((graph2 (InternalOriginalUniformDescentSelection.validity D) out raw parameter).iff
        (graph2 (InternalOriginalUniformDescentSelection.validity D)
          out shifted extendedParameter))))

/-- The target uses that SAME finalData, SAME outer Context, and SAME output.
The context guard is not removed; its input stays literally unchanged. -/
def TargetLaw (guard : Program 1) (p : GlobalSourcePackage.Inputs) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out raw shifted variableCode shiftedVariable typ index parameter extendedParameter
      context gamma extendedGamma addedType : OTerm alpha),
  let D := OriginalLambdaTraversalSelection.finalData (OriginalVariableLeaves.refineInputs guard p)
  Nonempty (Derivation body Delta
    ((Shape raw shifted variableCode shiftedVariable typ index parameter extendedParameter
        context gamma extendedGamma addedType).imp
      ((graph2 (InternalOriginalUniformDescentSelection.targetValidity D) out raw parameter).iff
        (graph2 (InternalOriginalUniformDescentSelection.targetValidity D)
          out shifted extendedParameter))))

/-- Retain EVERY conjunct of the preceding original-variable selection and
the complete native-accessibility/Package properties at the constructed input.
One initial tuple is chosen before all windows and runtime Gamma contexts. -/
def Properties (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
    (guard : Program 1) : Prop :=
  GlobalSourcePackage.InputsCalibrated n arity p ∧
  OriginalVariableLeaves.ContextGuardCalibrated n guard ∧
  GlobalSourcePackage.InputsCalibrated n arity (OriginalVariableLeaves.refineInputs guard p) ∧
  OriginalFinalNativeAccessibility.Properties n arity (OriginalVariableLeaves.refineInputs guard p) ∧
  OriginalVariableLeaves.BranchLaws guard p.base ∧
  (∀ v : List.Vector Nat 2,
    evaluate (OriginalVariableLeaves.refineInputs guard p).base.oldSource v =
      evaluate p.base.oldSource v ∧
    evaluate (OriginalVariableLeaves.refineInputs guard p).base.oldTarget v =
      evaluate p.base.oldTarget v) ∧
  SourceLaw guard p ∧ TargetLaw guard p

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableWeakening
