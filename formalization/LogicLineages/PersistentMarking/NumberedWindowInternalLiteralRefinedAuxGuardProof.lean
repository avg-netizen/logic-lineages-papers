module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectSelectorsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRefinedAuxGuardProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc zeroNeSuc sucNeZeroApply)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalBoundedDescentNormalizerStepSupportProof (conjunctionReject)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalAtomicRefinement
open NumberedWindowInternalAtomicRefinementObjectSelectorsProof (literalAddress)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeParsedEmitter (addressGood rawLeast)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelope (applyUnary nodeGood exactBody)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons unary z suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (takeUnary)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (canonicalCell)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private def clash (m n : Nat) (different : m ≠ n)
    (e : Derivation B Γ (eqn (numeral m : OTerm α) (numeral n))) : Derivation B Γ ⊥ := by
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => exact False.elim (different rfl)
    | succ n => exact zeroNeSuc e
  | succ m ih =>
    cases n with
    | zero => exact sucNeZeroApply e
    | succ n => exact ih n (fun same => different (congrArg Nat.succ same)) (cancelSuc e)

private theorem mismatch (x raw : OTerm α) (actual tag arity : Nat) (diff : actual ≠ tag)
    (select : Nonempty (Derivation B Γ (unary rawLeast raw x)))
    (known : Nonempty (Derivation B Γ (unary cellHead (numeral actual) raw)))
    (held : Nonempty (Derivation B Γ (unary (applyUnary (nodeGood (literal 1 tag) arity) rawLeast) (suc z) x))) :
    Nonempty (Derivation B Γ (⊥ : Formula α)) := by
  let K := literal 1 tag
  let test : Program 1 := .composition equalityTest ![cellHead,K]
  let size := applyUnary (exactBody arity) cellTail
  have row : Nonempty (Derivation B Γ
      (unary (conjunction cellGood (conjunction test size)) (suc z) raw)) :=
    takeUnary (nodeGood K arity) rawLeast (suc z) x raw held select
  obtain ⟨both⟩ := conjunctionRecover cellGood (conjunction test size) ![raw] row
  obtain ⟨flags⟩ := conjunctionRecover test size ![raw] ⟨Derivation.conjunctionRight both⟩
  have coded : Nonempty (Derivation B Γ (unary K (numeral tag) raw)) := literalGraph tag ![raw]
  have tests := compositionRecover equalityTest ![cellHead,K] (suc z) ![raw]
    ![numeral actual,numeral tag] ⟨Derivation.conjunctionLeft flags⟩
    (fun i => Fin.cases known (Fin.cases coded (fun q => Fin.elim0 q)) i)
  obtain ⟨e⟩ := equalityOfAcceptance (numeral actual) (numeral tag) tests
  exact ⟨clash actual tag diff e⟩

private theorem rejectAtom (x raw : OTerm α) (actual tag arity : Nat) (diff : actual ≠ tag)
    (select : Nonempty (Derivation B Γ (unary rawLeast raw x)))
    (known : Nonempty (Derivation B Γ (unary cellHead (numeral actual) raw))) :
    Nonempty (Derivation B Γ (unary (atomSource tag arity) z x)) := by
  let test := applyUnary (nodeGood (literal 1 tag) arity) rawLeast
  have ast : atomSource tag arity = conjunction addressGood (conjunction test storedTypeFits) := by
    unfold atomSource
    rw [exact_DispatchControlAST.2.2.2.2.2,exact_DispatchControlAST.2.2.2.2.2]
  rw [ast]
  apply conjunctionReject addressGood (conjunction test storedTypeFits) ![x]
  let H := unary (conjunction addressGood (conjunction test storedTypeFits)) (suc z) x
  have hp : Nonempty (Derivation B (H :: Γ) H) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨outer⟩ := conjunctionRecover addressGood (conjunction test storedTypeFits) ![x] hp
  obtain ⟨inner⟩ := conjunctionRecover test storedTypeFits ![x] ⟨Derivation.conjunctionRight outer⟩
  obtain ⟨bad⟩ := mismatch x raw actual tag arity diff (withHyp select H) (withHyp known H)
    ⟨Derivation.conjunctionLeft inner⟩
  exact ⟨Derivation.implicationIntroduction bad⟩

/-- The actual atom disambiguation is decided by the literal six at the
head of the held original raw least term, not external evaluation of a
packed address or its variable fields. -/
theorem exact_OpenRefinedTagSixGuardZeros (q raw : OTerm α)
    (select : Nonempty (Derivation B Γ (unary rawLeast raw q)))
    (known : Nonempty (Derivation B Γ (unary cellHead (numeral 6) raw))) :
    Nonempty (Derivation B Γ (unary freeSource z q)) ∧
      Nonempty (Derivation B Γ (unary bottomSource z q)) :=
  ⟨rejectAtom q raw 6 0 2 (by decide) select known,
    rejectAtom q raw 6 3 1 (by decide) select known⟩

theorem exact_OpenRefinedLiteralTagSixGuardZeros (ctx ty fields : OTerm α) :
    let raw := rawCons (numeral 6) fields
    let q := addressTerm ctx ty raw
    Nonempty (Derivation B Γ (unary freeSource z q)) ∧
      Nonempty (Derivation B Γ (unary bottomSource z q)) := by
  dsimp only
  let raw := rawCons (numeral 6) fields
  obtain ⟨h⟩ := canonicalCell (body := B) (Γ := Γ) (numeral 6) fields
  exact exact_OpenRefinedTagSixGuardZeros (addressTerm ctx ty raw) raw
    (literalAddress (body := B) (Γ := Γ) ctx ty raw).2.2.2
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight h)⟩

#print axioms exact_OpenRefinedTagSixGuardZeros
#print axioms exact_OpenRefinedLiteralTagSixGuardZeros
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRefinedAuxGuardProof
