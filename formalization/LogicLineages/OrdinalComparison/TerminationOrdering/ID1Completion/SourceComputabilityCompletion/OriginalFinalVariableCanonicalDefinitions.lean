module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableWeakeningDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonical
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors (graph1 graph2 graph3)
open InternalParameterizedCanonicalResultFold (foldGraph)
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion
open OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The original validity Program at the SAME final tuple after the once-only
all-input-equal variable-leaf refinement. This is not a replacement checker. -/
def originalSourceValidity (guard : Program 1) (p : GlobalSourcePackage.Inputs) : Program 2 :=
  InternalOriginalUniformDescentSelection.validity
    (OriginalLambdaTraversalSelection.finalData (OriginalVariableLeaves.refineInputs guard p))

/-- The original outer-window graph, whose context input is the left
coordinate of the original parameter. No runtime Gamma is captured. -/
def originalWindowGraph {alpha : Type} (p : GlobalSourcePackage.Inputs)
    (raw parameter : OTerm alpha) : Formula alpha :=
  OriginalVariableRepresentative.windowGraph p.window raw parameter

/-- All-output fixedness of the ACTUAL SAME-final fold at both the original
variable and its successor in the extended original Encodable context. Only
original shape, ORIGINAL source acceptance, and ORIGINAL window are premises.
In particular no shifted acceptance, fold result, or canonicality is assumed. -/
def FixednessLaw (guard : Program 1) (p : GlobalSourcePackage.Inputs) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out shiftedOut raw shifted variableCode shiftedVariable typ index parameter extendedParameter
      context gamma extendedGamma addedType : OTerm alpha),
  let D := OriginalLambdaTraversalSelection.finalData (OriginalVariableLeaves.refineInputs guard p)
  Nonempty (Derivation body Delta
    ((OriginalFinalVariableWeakening.Shape raw shifted variableCode shiftedVariable typ index
        parameter extendedParameter context gamma extendedGamma addedType ⊓
      (graph2 (originalSourceValidity guard p) (numeral 1) raw parameter ⊓
        originalWindowGraph p raw parameter)).imp
      (((foldGraph D out raw parameter).iff (equal out raw)) ⊓
        ((foldGraph D shiftedOut shifted extendedParameter).iff (equal shiftedOut shifted)))))

/-- Actual literal packed shift/erasure graphs are constructed, not inferred
from endpoint shape alone. Every arbitrary shift-canonicalize-erase-canonicalize
chain uses that SAME final fold at its actual parameter, and agrees with the
actual original final-fold output. These are payloads, not native Objects. -/
def CancellationLaw (guard : Program 1) (p : GlobalSourcePackage.Inputs) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (shiftOut canonicalShift erased out originalOut raw shifted variableCode shiftedVariable
      typ index parameter extendedParameter context gamma extendedGamma addedType : OTerm alpha),
  let D := OriginalLambdaTraversalSelection.finalData (OriginalVariableLeaves.refineInputs guard p)
  Nonempty (Derivation body Delta
    ((OriginalFinalVariableWeakening.Shape raw shifted variableCode shiftedVariable typ index
        parameter extendedParameter context gamma extendedGamma addedType ⊓
      (graph2 (originalSourceValidity guard p) (numeral 1) raw parameter ⊓
        originalWindowGraph p raw parameter)).imp
      (graph2 shiftPackedRaw shifted (numeral 0) raw ⊓
        (graph3 erasePackedRaw raw addedType (numeral 0) shifted ⊓
          ((graph2 shiftPackedRaw shiftOut (numeral 0) raw ⊓
            (foldGraph D canonicalShift shiftOut extendedParameter ⊓
              (graph3 erasePackedRaw erased addedType (numeral 0) canonicalShift ⊓
                (foldGraph D out erased parameter ⊓ foldGraph D originalOut raw parameter)))).imp
            (equal out originalOut))))))

/-- Independent internal preservation of the original variable-occurrence
rank, with all symbolic rank outputs, at both actual SAME-final endpoints.
The original and shifted payloads and their canonical outputs all have rank
one. No native evaluation or semantic reflection occurs in this statement. -/
def RankLaw (guard : Program 1) (p : GlobalSourcePackage.Inputs) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (rank out shiftedOut raw shifted variableCode shiftedVariable typ index parameter extendedParameter
      context gamma extendedGamma addedType : OTerm alpha),
  let D := OriginalLambdaTraversalSelection.finalData (OriginalVariableLeaves.refineInputs guard p)
  Nonempty (Derivation body Delta
    ((OriginalFinalVariableWeakening.Shape raw shifted variableCode shiftedVariable typ index
        parameter extendedParameter context gamma extendedGamma addedType ⊓
      (graph2 (originalSourceValidity guard p) (numeral 1) raw parameter ⊓
        originalWindowGraph p raw parameter)).imp
      (((graph1 variableRankPackedRaw rank raw).iff (equal rank (numeral 1))) ⊓
        (((graph1 variableRankPackedRaw rank shifted).iff (equal rank (numeral 1))) ⊓
          ((foldGraph D out raw parameter ⊓ foldGraph D shiftedOut shifted extendedParameter).imp
            (((graph1 variableRankPackedRaw rank out).iff
                (graph1 variableRankPackedRaw rank raw)) ⊓
              ((graph1 variableRankPackedRaw rank shiftedOut).iff
                (graph1 variableRankPackedRaw rank shifted))))))))

/-- Explicit retention of the entire previously selected native Package,
cancellation, rank, accessibility and least-model claims at the SAME input. -/
def NativeProperties (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
    (guard : Program 1) : Prop :=
  OriginalFinalNativeAccessibility.Properties n arity (OriginalVariableLeaves.refineInputs guard p)

/-- One initial tuple is selected before all windows and runtime contexts.
EVERY preceding weakening/variable/native property is retained without
reselecting a representative or changing any final Program. -/
def Properties (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
    (guard : Program 1) : Prop :=
  OriginalFinalVariableWeakening.Properties n arity p guard ∧
  NativeProperties n arity p guard ∧
  FixednessLaw guard p ∧ CancellationLaw guard p ∧ RankLaw guard p

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonical
