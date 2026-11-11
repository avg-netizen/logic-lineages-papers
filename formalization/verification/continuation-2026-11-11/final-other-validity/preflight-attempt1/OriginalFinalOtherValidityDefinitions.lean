module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalOtherValidity
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open UniformCertificateCompletion
open OriginalTransparentLambdaValidityInternal (BooleanOutput)

/-- Full-output exposure of the original source at the SAME final tuple.
The sole antecedent is acceptance by the EXISTING literal OTHER-tag AST.
The original bottom/member-normalized source and target leaves both remain
on the factor side. No transformed-input acceptance is assumed or proved. -/
def SourceOtherLaw (p : GlobalSourcePackage.Inputs) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out raw parameter : OTerm alpha),
  let D := OriginalLambdaTraversalSelection.finalData p
  let N := OriginalHereditaryValidity.normalizedData p.base
  Nonempty (Derivation body Delta
    ((graph1 OriginalLambdaTraversalInternal.otherTag InternalOriginalStepGuard.one raw).imp
      ((graph2 (InternalOriginalUniformDescentSelection.validity D) out raw parameter).iff
        (BooleanOutput out
          (graph2 N.oldSource InternalOriginalStepGuard.one raw parameter ⊓
            graph2 N.oldTarget InternalOriginalStepGuard.one raw parameter)))))

/-- Full-output exposure of the original target at that IDENTICAL final
Data. The exact normalized oldTarget is retained with no source membership,
source-validity, native calibration, successful-run or output-one premise. -/
def TargetOtherLaw (p : GlobalSourcePackage.Inputs) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out raw parameter : OTerm alpha),
  let D := OriginalLambdaTraversalSelection.finalData p
  let N := OriginalHereditaryValidity.normalizedData p.base
  Nonempty (Derivation body Delta
    ((graph1 OriginalLambdaTraversalInternal.otherTag InternalOriginalStepGuard.one raw).imp
      ((graph2 (InternalOriginalUniformDescentSelection.targetValidity D) out raw parameter).iff
        (BooleanOutput out (graph2 N.oldTarget InternalOriginalStepGuard.one raw parameter)))))

/- FROZEN EXPOSURE SPECIFICATION, NOT AN ACCEPTANCE CLAIM.

D is literally OriginalLambdaTraversalSelection.finalData p, hence the
OuterSelection data of OriginalLambdaTraversalSelection.finalInputs p.
N is literally normalizeData (BottomParameter.baseData p.base), through the
already frozen OriginalHereditaryValidity.normalizedData definition. The
universal p quantifier specializes to the existing globally selected p and
retains its whole Package without choosing or changing any selector.

These statements expose the remaining original source/target leaves only.
They do not prove transformed acceptance, canonical cancellation, primary
search transport, substitution/I transport or the closed paper06 theorem.
Primary equivalence is not a strict step. The original certificate checker
continues to require a strict step plus representatives.
-/
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalOtherValidity
