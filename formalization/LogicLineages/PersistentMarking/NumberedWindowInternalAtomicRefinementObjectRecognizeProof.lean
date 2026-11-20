module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectSelectorsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectRecognizeProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalAcceptance (conjunction constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeReject)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open NumberedWindowInternalProbeTargets (OTerm)
open NumberedWindowInternalAtomicRefinement NumberedWindowInternalAtomicRefinementObjectTargets
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph unaryInput)
open NumberedWindowInternalAtomicRefinementObjectSelectorsProof (inverseEq literalAddress literalAtom toFree)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeParsedEmitter (addressGood rawLeast)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelope (applyUnary nodeGood exactBody)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody takeUnary)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (canonicalCell)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private def innerFreeTest : Program 1 := applyUnary (nodeGood (literal 1 0) 2) rawLeast

/-- The actual tested raw tag of the literal bottom is THREE. A ONE
output from the actual free tag/arity branch would therefore derive
the arithmetic contradiction THREE = ZERO. -/
private theorem rejectInner (x k : OTerm α)
    (hk : Nonempty (Derivation body Γ (unary rawLeast k x)))
    (head : Nonempty (Derivation body Γ (unary cellHead (numeral 3) k))) :
    Nonempty (Derivation body Γ (unary innerFreeTest (suc z) x).not) := by
  let H := unary innerFreeTest (suc z) x
  let tag := literal 1 0
  let tagTest : Program 1 := .composition equalityTest ![cellHead,tag]
  let sizeTest := applyUnary (exactBody 2) cellTail
  obtain ⟨localRaw⟩ := hk
  obtain ⟨localHead⟩ := head
  have row := takeUnary (body := body) (Γ := H :: Γ) (nodeGood tag 2) rawLeast (suc z) x k
    ⟨Derivation.hypothesis List.mem_cons_self⟩ ⟨addHyp localRaw H⟩
  have guarded : Nonempty (Derivation body (H :: Γ)
      (unary (conjunction cellGood (conjunction tagTest sizeTest)) (suc z) k)) := row
  obtain ⟨both⟩ := conjunctionRecover cellGood (conjunction tagTest sizeTest) ![k] guarded
  obtain ⟨flags⟩ := conjunctionRecover tagTest sizeTest ![k] ⟨Derivation.conjunctionRight both⟩
  have tagOk : Nonempty (Derivation body (H :: Γ) (unary tagTest (suc z) k)) :=
    ⟨Derivation.conjunctionLeft flags⟩
  have expectedZero : Nonempty (Derivation body (H :: Γ) (unary tag z k)) := literalGraph 0 ![k]
  have test := compositionRecover equalityTest (![cellHead,tag] : Fin 2 → Program 1)
    (suc z) ![k] ![numeral 3,z] tagOk
    (fun i => Fin.cases (show Nonempty (Derivation body (H :: Γ) (unary cellHead (numeral 3) k))
      from ⟨addHyp localHead H⟩) (Fin.cases expectedZero (fun j => Fin.elim0 j)) i)
  obtain ⟨bad⟩ := equalityOfAcceptance (numeral 3) z test
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply bad)⟩

private theorem missFreeBottom (c t : OTerm α) :
    Nonempty (Derivation body Γ (unary freeSource z (packedBottomTerm c t))) := by
  let k := rawCons (numeral 3) (packedBody [t])
  let x := addressTerm c t k
  let check := innerFreeTest
  let secondary := conjunction check storedTypeFits
  have ast : freeSource =
      ID1Completion.InternalAcceptance.branch (normalize addressGood) (constantZero 1) (normalize secondary) := by
    unfold freeSource atomSource
    rw [exact_DispatchControlAST.2.2.2.2.2,exact_DispatchControlAST.2.2.2.2.2] <;> rfl
  obtain ⟨outer,_,_,hk⟩ := literalAddress (body := body) (Γ := Γ) c t k
  obtain ⟨cell⟩ := canonicalCell (body := body) (Γ := Γ) (numeral 3) (packedBody [t])
  have head : Nonempty (Derivation body Γ (unary cellHead (numeral 3) k)) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight cell)⟩
  obtain ⟨notInner⟩ := rejectInner x k hk head
  let H := unary secondary (suc z) x
  have h : Nonempty (Derivation body Γ H.not) := by
    obtain ⟨acceptsPair⟩ := conjunctionRecover (body := body) (Gamma := H :: Γ)
      check storedTypeFits ![x] ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction
      (Derivation.implicationElimination (addHyp notInner H) (Derivation.conjunctionLeft acceptsPair))⟩
  change Nonempty (Derivation body Γ (unary freeSource z x))
  rw [ast]
  exact successorBranchIntro (normalize addressGood) (constantZero 1) (normalize secondary)
    z z ![x] (ID1Completion.InternalAcceptanceNormalizationProof.normalizeAccept addressGood ![x] outer)
    (normalizeReject secondary ![x] h)

private theorem toBottom (x c t : OTerm α)
    (e : Nonempty (Derivation body Γ (equal x (packedBottomTerm c t)))) :
    Nonempty (Derivation body Γ
      (programGraph freeSource (numeral 0) ![x] ⊓ programGraph bottomSource (numeral 1) ![x])) := by
  let b := packedBottomTerm c t
  have same := inverseEq x b e
  have known : Nonempty (Derivation body Γ (unary bottomSource (suc z) b)) :=
    (literalAtom (body := body) (Γ := Γ) 3 c t []).1
  obtain ⟨left⟩ := unaryInput freeSource z b x same (missFreeBottom c t)
  obtain ⟨right⟩ := unaryInput bottomSource (suc z) b x same known
  exact ⟨Derivation.conjunctionIntroduction left right⟩

theorem exactRecognition : ExactOpenAtomicRecognition := by
  exact ⟨fun _ _ _ => toFree,fun _ _ _ => toBottom⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectRecognizeProof
