module

public import LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankFinishTransferProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputWalkProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationSuccessorProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankPositiveTransferProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open ID1Completion.InternalControlGraphSupportProof (programRename compositionValue projectionValue outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalEqualityTestCompositionProof (equalityOfEqual)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open NumberedWindowInternalSparsePositiveOutputTargets (args4 args5)
open NumberedWindowInternalSparsePositiveOutputWalkProof (succAt succAtValue)
open NumberedWindowInternalSparsePositiveIterationSuccessorProof (loopArgsRename)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalZeroRankAdvance (zeroOutput)
open NumberedWindowInternalParameterizedPositiveFold
open NumberedWindowInternalZeroRankStepTransportProof (Report)
open NumberedWindowInternalZeroRankFinishTransferProof (exact_OpenZeroRankFinishTransfer)

attribute [local irreducible] programGraph

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private abbrev picks : Fin 4 → Program 5 :=
  ![.projection 0,.projection 1,succAt 2,.projection 3]

private theorem picksKnown (c ty source cert target : OTerm α) (i : Fin 4) :
    Report (B := B) (Γ := Γ) (picks i) (args4 c ty (suc source) cert i) (args5 c ty source cert target) := by
  let xs := args5 c ty source cert target
  exact Fin.cases (projectionValue (0 : Fin 5) xs)
    (Fin.cases (projectionValue (1 : Fin 5) xs) (Fin.cases (succAtValue (2 : Fin 5) xs)
      (Fin.cases (projectionValue (3 : Fin 5) xs) (fun q => Fin.elim0 q)))) i

private theorem exact_WalkTransfer (g : Program 1) (raw : Program 5) (least : Program 3)
    (c ty source cert target : OTerm α)
    (held : Report (B := B) (Γ := Γ) (walkAt (zeroOutput g (advance raw least))) (suc target)
      (args5 c ty source cert target)) :
    Report (B := B) (Γ := Γ) (walkAt (advance raw least)) (suc target) (args5 c ty source cert target) := by
  let A := zeroOutput g (advance raw least)
  let U := advance raw least
  let xs := args5 c ty source cert target
  let ys := args4 c ty (suc source) cert
  have f := compositionRecover (finishAt A) picks (suc target) xs ys held
    (picksKnown c ty source cert target)
  have h := exact_OpenZeroRankFinishTransfer g raw least c ty (suc source) cert target f
  exact compositionValue (finishAt U) picks (suc target) xs ys h (picksKnown c ty source cert target)

private def nonempty : Program 5 := branch (.projection 3) (constantZero 5) (constantOne 5)
private abbrev comparison (A : Program 4) : Fin 2 → Program 5 := ![walkAt A,succAt 4]
private def test (A : Program 4) : Program 5 := .composition equalityTest (comparison A)

private theorem comparisonKnown (A : Program 4) (c ty source cert target current : OTerm α)
    (walk : Report (B := B) (Γ := Γ) (walkAt A) current (args5 c ty source cert target))
    (j : Fin 2) : Report (B := B) (Γ := Γ) (comparison A j) (![current,suc target] j)
        (args5 c ty source cert target) :=
  Fin.cases walk
    (Fin.cases (succAtValue (4 : Fin 5) (args5 c ty source cert target)) (fun k => Fin.elim0 k)) j

private theorem pickedTransfer (g : Program 1) (raw : Program 5) (least : Program 3)
    (c ty source cert target current : OTerm α)
    (guard : Report (B := B) (Γ := Γ) nonempty (suc z) (args5 c ty source cert target))
    (held : Report (B := B) (Γ := Γ) (test (zeroOutput g (advance raw least))) (suc z)
      (args5 c ty source cert target))
    (walk : Report (B := B) (Γ := Γ) (walkAt (zeroOutput g (advance raw least))) current
      (args5 c ty source cert target)) :
    Report (B := B) (Γ := Γ) (positiveAt (advance raw least)) (suc z) (args5 c ty source cert target) := by
  let A := zeroOutput g (advance raw least)
  let U := advance raw least
  let xs := args5 c ty source cert target
  have ok := compositionRecover equalityTest (comparison A) (suc z) xs ![current,suc target] held
    (comparisonKnown A c ty source cert target current walk)
  have e := equalityOfAcceptance current (suc target) ok
  have w := outputTransport (walkAt A) current (suc target) xs e walk
  have ordinary := exact_WalkTransfer g raw least c ty source cert target w
  have succeeds := equalityOfEqual (suc target) (suc target) (body := B) (Gamma := Γ)
    ⟨ID1Completion.InternalTagArithmeticSupportProof.refl (suc target)⟩
  have t := compositionValue equalityTest (comparison U) (suc z) xs
    ![suc target,suc target] succeeds (comparisonKnown U c ty source cert target (suc target) ordinary)
  exact conjunctionAccept nonempty (test U) xs guard t

/-- Genuine arithmetic derivation on the original input and certificate;
proved by object-language induction, not by reflecting Lean evaluation. -/
theorem exact_OpenZeroRankPositiveImpliesOrdinary (g : Program 1) (raw : Program 5) (least : Program 3)
    (c ty source cert target : OTerm α)
    (held : Report (B := B) (Γ := Γ) (zeroPositive g raw least) (suc z) (args5 c ty source cert target)) :
    Report (B := B) (Γ := Γ) (NumberedWindowInternalSparsePositiveFold.positive raw least) (suc z)
      (args5 c ty source cert target) := by
  rw [← exact_OriginalParameterizedPositive]
  let A := zeroOutput g (advance raw least)
  obtain ⟨both⟩ := conjunctionRecover nonempty (test A) (args5 c ty source cert target) held
  apply programCases (walkAt A) (args5 c ty source cert target) _
  intro β j Δ current keep graph
  simp only [programRename,zRelabel,ID1Completion.InternalTagArithmeticSyntaxProof.sucRelabel,
    loopArgsRename]
  rw [loopArgsRename] at graph
  have first := renameInto (Nonempty.intro (Derivation.conjunctionLeft both)) j Δ keep
  have second := renameInto (Nonempty.intro (Derivation.conjunctionRight both)) j Δ keep
  simp only [programRename,zRelabel,ID1Completion.InternalTagArithmeticSyntaxProof.sucRelabel,
    loopArgsRename] at first second
  exact pickedTransfer g raw least (c.relabel j) (ty.relabel j) (source.relabel j)
    (cert.relabel j) (target.relabel j) current first second graph

#print axioms exact_OpenZeroRankPositiveImpliesOrdinary
end LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankPositiveTransferProof
