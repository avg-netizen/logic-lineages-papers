module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicResidualProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicShapeDecodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectSelectorsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphExtensionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralAtomProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open SourceComputabilityFormulaSupportProof (numeral)
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourcePresentation (Data)
open ID1Completion.InternalAccessibilityRules (carrier)
open ID1Completion.InternalControlGraphSupportProof (compositionValue headTransport)
open ID1Completion.InternalAcceptance (branch conjunction constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (rejectForwardOrder rejectBackwardOrder)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalOriginalOrderProof (actualOriginalOrderIntroduction)
open ID1Completion.InternalRecursionGraphExtensionSupportProof (successorOrder)
open ID1Completion.InternalAdditionLawsProof (leftZero)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeParsedEmitter (addressGood rawLeast)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparsePathEnvelope (applyUnary)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody makeUnary)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (canonicalCell)
open NumberedWindowInternalAtomicRefinementObjectSelectorsProof (literalAddress)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalNeutralFactsTargets (atom direct inherited)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalLiteralNeutralResidualProof (Residual)
open NumberedWindowInternalLiteralAtomicResidualProof (AtomBody AtomStep exact_LiteralAtomicResidual)
open NumberedWindowInternalNeutralFactsSyntaxProof (atomRename)
open NumberedWindowInternalAtomicRefinement (freeSource bottomSource)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (D)
open NumberedWindowInternalLiteralAtomicShapeDecodeProof (exact_OpenLiteralAtomicShapeDecode)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

def rawHeader : Program 1 := applyUnary cellHead rawLeast
def lambdaHeader : Program 1 := .composition equalityTest ![rawHeader,literal 1 2]
def notLambdaHeader : Program 1 := branch lambdaHeader (literal 1 1) (constantZero 1)

/-- The actual neutral recognizer inspects the original address shell
and the head tag of its literal raw least, rejecting the lambda tag.
This choice is auxiliary to the object proof, not a new rewrite rule. -/
def neutralSource : Program 1 := conjunction addressGood notLambdaHeader

theorem zeroBelowSuccessor (t : OTerm α) : D B Γ (ltF z (suc t)) := by
  apply actualOriginalOrderIntroduction B α Γ z (suc t) t
  rw [onEquality]
  exact ⟨leftZero (suc t)⟩

theorem literalHead (tag : Nat) (c t : OTerm α) (fields : List (OTerm α)) :
    let k := rawCons (numeral tag) (packedBody fields)
    let x := addressTerm c t k
    D B Γ (unary addressGood (suc z) x) ∧ D B Γ (unary rawHeader (numeral tag) x) := by
  let k := rawCons (numeral tag) (packedBody fields)
  let x := addressTerm c t k
  obtain ⟨good,_,_,raw⟩ := literalAddress (body := B) (Γ := Γ) c t k
  obtain ⟨cell⟩ := canonicalCell (body := B) (Γ := Γ) (numeral tag) (packedBody fields)
  have h : D B Γ (unary cellHead (numeral tag) k) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight cell)⟩
  exact ⟨good,makeUnary cellHead rawLeast (numeral tag) x k h raw⟩

theorem neutralFromHeader (x h : OTerm α)
    (good : D B Γ (unary addressGood (suc z) x))
    (head : D B Γ (unary rawHeader h x))
    (notLambda : D B Γ (programGraph equalityTest z (Fin.cons h (Fin.cons (numeral 2) Fin.elim0)))) :
    D B Γ (atom neutralSource x) := by
  have reject : D B Γ (unary lambdaHeader z x) := by
    apply compositionValue equalityTest ![rawHeader,literal 1 2] z ![x] ![h,numeral 2] notLambda
    intro i
    exact Fin.cases head (Fin.cases (literalGraph 2 ![x]) (fun j => Fin.elim0 j)) i
  have accepted : D B Γ (unary notLambdaHeader (suc z) x) :=
    zeroBranchIntro lambdaHeader (literal 1 1) (constantZero 1) (suc z) ![x]
      reject (literalGraph 1 ![x])
  exact conjunctionAccept addressGood notLambdaHeader ![x] good accepted

/-- An arbitrary reported bottom is recognized by the actual neutral
test after opening its physical address and raw constructor. -/
theorem exact_OpenLiteralBottomNeutral (x : OTerm α) (known : D B Γ (atom bottomSource x)) :
    D B Γ (atom neutralSource x) := by
  apply exact_OpenLiteralAtomicShapeDecode 3 0 x (atom neutralSource x) known
  intro β j Δ c t tail _ length shape
  rcases tail with _ | ⟨d,tail⟩ <;> simp at length
  rw [atomRename]
  obtain ⟨shell,head⟩ := literalHead (B := B) (Γ := Δ) 3 c t [t]
  have small : D B Δ (ltF (numeral 2 : OTerm β) (numeral 3)) :=
    successorOrder (numeral 1) (numeral 2)
      (successorOrder (numeral 0) (numeral 1) (zeroBelowSuccessor (z : OTerm β)))
  have n := neutralFromHeader _ (numeral 3) shell head (rejectBackwardOrder (numeral 3) (numeral 2) small)
  obtain ⟨e⟩ := shape
  exact headTransport neutralSource (suc z) _ (x.relabel j) ![] ⟨symm e⟩ n

/-- An arbitrary reported free variable is neutral in the same test. -/
theorem exact_OpenLiteralVariableNeutral (x : OTerm α) (known : D B Γ (atom freeSource x)) :
    D B Γ (atom neutralSource x) := by
  apply exact_OpenLiteralAtomicShapeDecode 0 1 x (atom neutralSource x) known
  intro β j Δ c t tail _ length shape
  rcases tail with _ | ⟨n,_ | ⟨d,tail⟩⟩ <;> simp at length
  rw [atomRename]
  obtain ⟨shell,head⟩ := literalHead (B := B) (Γ := Δ) 0 c t [t,n]
  have small : D B Δ (ltF z (numeral 2 : OTerm β)) := zeroBelowSuccessor (numeral 1)
  have n := neutralFromHeader _ (numeral 0) shell head (rejectForwardOrder (numeral 0) (numeral 2) small)
  obtain ⟨e⟩ := shape
  exact headTransport neutralSource (suc z) _ (x.relabel j) ![] ⟨symm e⟩ n

/-- With the actual non-lambda recognizer chosen, the direct-step
and neutral clauses of BOTH atoms are discharged. Only the two
application clauses remain here; positive forward transport remains
a different obligation of the computability argument. -/
structure NeutralApplications (s : Data) (p h : Program 3) (c : Nat) : Prop where
  closure : ∀ (α : Type) (Γ : List (Formula α)) (x u y : OTerm α),
    NumberedWindowInternalNeutralFactsTargets.D s c Γ (atom neutralSource x) →
    NumberedWindowInternalNeutralFactsTargets.D s c Γ (accepts p x u y) →
    NumberedWindowInternalNeutralFactsTargets.D s c Γ (carrier s false c y) ∧
    NumberedWindowInternalNeutralFactsTargets.D s c Γ (atom neutralSource y)
  inversion : ∀ (α : Type) (Γ : List (Formula α)) (x u t y : OTerm α),
    NumberedWindowInternalNeutralFactsTargets.D s c Γ (atom neutralSource x) →
    NumberedWindowInternalNeutralFactsTargets.D s c Γ (accepts p x u t) →
    NumberedWindowInternalNeutralFactsTargets.D s c Γ (direct s h c t y) →
    NumberedWindowInternalNeutralFactsTargets.D s c Γ (atom bottomSource y ⊔ inherited s p h c x u y)

theorem exact_LiteralNeutralFromApplications (i cv tv : Program 1) (raw : Program 5) (L p : Program 3)
    (c : Nat) (pending : NeutralApplications (AtomBody i cv tv raw L) p (AtomStep i cv tv raw L) c) :
    Residual (AtomBody i cv tv raw L) p (AtomStep i cv tv raw L) neutralSource bottomSource c :=
  exact_LiteralAtomicResidual i cv tv raw L p neutralSource c
    ⟨fun α Γ x => exact_OpenLiteralBottomNeutral x,
      fun α Γ x => exact_OpenLiteralVariableNeutral x,
      pending.closure,pending.inversion⟩

#print axioms exact_LiteralNeutralFromApplications
#print axioms exact_OpenLiteralBottomNeutral
#print axioms exact_OpenLiteralVariableNeutral
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralAtomProof
