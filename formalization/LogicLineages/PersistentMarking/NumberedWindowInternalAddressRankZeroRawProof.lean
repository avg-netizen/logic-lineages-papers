module
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAddressRankDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressThinDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatchSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormulaSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAddressRankZeroRawProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalAcceptance (branch conjunction constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalFixedWindowVertexDispatch (constant)
open ID1Completion.InternalFixedWindowVertexDispatchSupportProof (constantValue)
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply symm)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary z suc)
open NumberedWindowInternalSparsePathEnvelope (applyUnary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename inputsRename)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalFreshProbeParsedEmitter (addressGood rawLeast rawContext rawResult)
open NumberedWindowInternalAtomicRefinement (freeSource bottomSource)
open NumberedWindowInternalNeutralAddressRank (addressRank)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar shapeChecks coordinateCall)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem retainZero (test plain : Program 1) (m : Nat) (q : OTerm α)
    (held : Nonempty (Derivation B Γ (unary (branch test plain (constant 1 (m+1))) z q))) :
    Nonempty (Derivation B Γ (unary plain z q)) := by
  apply optionGraphCases test ![q] _
  · intro β j Δ keep zero
    rw [inputsRename] at zero
    rw [unaryRename,zRelabel]
    have moved := renameInto held j Δ keep
    rw [unaryRename,zRelabel] at moved
    exact zeroBranchElim test plain (constant 1 (m+1)) z ![q.relabel j] zero moved
  · intro β j Δ v keep bit
    rw [inputsRename] at bit
    rw [unaryRename,zRelabel]
    have moved := renameInto held j Δ keep
    rw [unaryRename,zRelabel] at moved
    have bad := successorBranchElim test plain (constant 1 (m+1)) z v ![q.relabel j] bit moved
    obtain ⟨eq⟩ := valueUnique (constant 1 (m+1)) z (numeral (m+1)) ![q.relabel j]
      bad (constantValue 1 (m+1) ![q.relabel j])
    exact ⟨Derivation.explosion (sucNeZeroApply (symm eq))⟩

/-- The actual scalar's rank zero, at a real checked tag-three address,
is zero at that same physical raw least field. Positive bare overrides
are excluded internally, not by numeral evaluation or reflection. -/
theorem exact_OpenRawRankFromAddressZero (g : Program 1) (q k : OTerm α)
    (valid : Nonempty (Derivation B Γ (unary addressGood (suc z) q)))
    (field : Nonempty (Derivation B Γ (unary rawLeast k q)))
    (rankZero : Nonempty (Derivation B Γ (unary (addressRank g) z q))) :
    Nonempty (Derivation B Γ (unary g z k)) := by
  let inner := branch addressGood (constantZero 1) (applyUnary g rawLeast)
  have notFree := retainZero freeSource (branch bottomSource inner (constant 1 1)) 1 q rankZero
  have notBottom := retainZero bottomSource inner 0 q notFree
  have tested := successorBranchElim addressGood (constantZero 1) (applyUnary g rawLeast) z z ![q]
    valid notBottom
  apply compositionRecover g (fun _ : Fin 1 => rawLeast) z ![q] ![k] tested
  intro i
  obtain rfl := Fin.eq_zero i
  exact field

theorem exact_OpenPhysicalScalarAddressGood (cv tv : Program 1) (W L : Program 3) (q : OTerm α)
    (held : Nonempty (Derivation B Γ (unary (addressScalar cv tv W L) (suc z) q))) :
    Nonempty (Derivation B Γ (unary addressGood (suc z) q)) := by
  obtain ⟨pieces⟩ := conjunctionRecover (shapeChecks cv tv) (coordinateCall W L) ![q] held
  obtain ⟨shell⟩ := conjunctionRecover addressGood
    (conjunction (applyUnary cv rawContext) (applyUnary tv rawResult)) ![q]
    ⟨Derivation.conjunctionLeft pieces⟩
  exact ⟨Derivation.conjunctionLeft shell⟩

#print axioms exact_OpenRawRankFromAddressZero
#print axioms exact_OpenPhysicalScalarAddressGood
end LogicLineages.PersistentMarking.NumberedWindowInternalAddressRankZeroRawProof
