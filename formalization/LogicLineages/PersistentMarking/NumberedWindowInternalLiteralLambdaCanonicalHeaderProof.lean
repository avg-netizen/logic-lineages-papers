module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralAtomProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastReflectsHeaderProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaCanonicalHeaderProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalControlGraphSupportProof (outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename inputsRename)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseAddressPositiveOpenBindingProof (addressReportRename)
open NumberedWindowInternalLiteralNeutralAtomProof (rawHeader lambdaHeader)
open NumberedWindowInternalNeutralFactsTargets (atom)
open NumberedWindowInternalNeutralFactsSyntaxProof (atomRename)
open NumberedWindowInternalFreshProbeParsedEmitter (rawLeast)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (D)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- At the original scalar address's exact reported least field, the
literal successful lambda test reads the actual header of that field. -/
theorem exact_OpenCanonicalLambdaHeader (x ctx ty k : OTerm α)
    (shape : D B Γ (atom lambdaHeader x)) (atX : D B Γ (addressReport x ctx ty k)) :
    D B Γ (unary cellHead (numeral 2) k) := by
  apply programCases rawHeader ![x] _
  intro β j Δ h keep graph
  rw [inputsRename] at graph
  rw [unaryRename,numeralRename]
  have passed := renameInto shape j Δ keep
  rw [atomRename] at passed
  have addressed := renameInto atX j Δ keep
  rw [addressReportRename] at addressed
  obtain ⟨fields⟩ := addressed
  let address := x.relabel j
  let term := k.relabel j
  have checked : D B Δ (unary rawLeast term address) :=
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight fields))⟩
  have e := equalityOfAcceptance h (numeral 2)
    (compositionRecover equalityTest ![rawHeader,literal 1 2] (suc z) ![address] ![h,numeral 2] passed
      (fun i => Fin.cases graph (Fin.cases (literalGraph 2 ![address]) (fun k => Fin.elim0 k)) i))
  have head : D B Δ (unary cellHead h term) := by
    apply compositionRecover cellHead (fun _ : Fin 1 => rawLeast) h ![address] ![term] graph
    intro i
    obtain rfl := Fin.eq_zero i
    exact checked
  exact outputTransport cellHead h (numeral 2) ![term] e head

#print axioms exact_OpenCanonicalLambdaHeader
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaCanonicalHeaderProof
