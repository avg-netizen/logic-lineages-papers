module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TypedPrimaryEdge.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.InternalSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof InternalAcceptanceNormalizationProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
abbrev OT := InternalGraphComposition.OTerm

def afterLambda : Program 19 := choose (tagIs 2) applicationCase
  (choose (tagIs 4) ordinaryCase (choose (tagIs 5) numberedCase
    (choose (tagIs 7) applicationCase (InternalAcceptance.constantZero 19))))
def dispatch : Program 19 := choose (tagIs 1) lambdaCase afterLambda

theorem constantEq (k : Nat) : constant k = OriginalRawSyntaxTransport.constant 19 k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [constant,OriginalRawSyntaxTransport.constant,ih]

theorem projectionAt (i : Fin 19) (xs : Fin 19 → OT alpha) (value : OT alpha)
    (h : Nonempty (Derivation body Delta (eqn (xs i) value))) :
    Nonempty (Derivation body Delta (programGraph (.projection i) value xs)) :=
  outputTransport (.projection i) (xs i) value xs h (projectionValue i xs)

theorem eqAccept (i j : Fin 19) (xs : Fin 19 → OT alpha)
    (h : Nonempty (Derivation body Delta (eqn (xs i) (xs j)))) :
    Nonempty (Derivation body Delta (programGraph (eqField i j) (suc z) xs)) :=
  binaryValue InternalEqualityTest.equalityTest (.projection i) (.projection j) (suc z) (xs i) (xs j) xs
    (InternalEqualityTestCompositionProof.equalityOfEqual _ _ h) (projectionValue i xs) (projectionValue j xs)

theorem eqRecover (i j : Fin 19) (xs : Fin 19 → OT alpha)
    (h : Nonempty (Derivation body Delta (programGraph (eqField i j) (suc z) xs))) :
    Nonempty (Derivation body Delta (eqn (xs i) (xs j))) :=
  InternalEqualityTestProof.equalityOfAcceptance _ _
    (binaryRecover InternalEqualityTest.equalityTest (.projection i) (.projection j) (suc z) (xs i) (xs j) xs
      h (projectionValue i xs) (projectionValue j xs))

theorem projectionRecover (i : Fin 19) (xs : Fin 19 → OT alpha)
    (h : Nonempty (Derivation body Delta (programGraph (.projection i) (suc z) xs))) :
    Nonempty (Derivation body Delta (eqn (xs i) (suc z))) :=
  valueUnique (.projection i) (xs i) (suc z) xs (projectionValue i xs) h

theorem chooseAccept (p yes no : Program 19) (xs : Fin 19 → OT alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p (suc z) xs))) :
    (Nonempty (Derivation body Delta (programGraph (choose p yes no) (suc z) xs)) ↔
     Nonempty (Derivation body Delta (programGraph yes (suc z) xs))) :=
  ⟨successorBranchElim p no yes (suc z) z xs hp,
    successorBranchIntro p no yes (suc z) z xs hp⟩

theorem chooseNumeral (tag k : Nat) (yes no : Program 19) (xs : Fin 19 → OT alpha)
    (ht : Nonempty (Derivation body Delta (eqn (xs 0) (numeral tag)))) :
    (Nonempty (Derivation body Delta (programGraph (choose (tagIs k) yes no) (suc z) xs)) ↔
     Nonempty (Derivation body Delta (programGraph (if tag = k then yes else no) (suc z) xs))) := by
  have hp := projectionAt 0 xs (numeral tag) ht
  simp only [choose,tagIs,constantEq]
  exact ⟨OriginalRawSyntaxTransportInternalConstructorSupportProof.branchNumeralElim tag k
    (.projection 0) no yes (suc z) xs hp,
    OriginalRawSyntaxTransportInternalConstructorSupportProof.branchNumeralIntro tag k
      (.projection 0) no yes (suc z) xs hp⟩

theorem bothRecover (p q : Program 19) (xs : Fin 19 → OT alpha)
    (h : Nonempty (Derivation body Delta (programGraph (both p q) (suc z) xs))) :
    Nonempty (Derivation body Delta (programGraph p (suc z) xs ⊓ programGraph q (suc z) xs)) :=
  conjunctionRecover p q xs h

theorem bothAccept (p q : Program 19) (xs : Fin 19 → OT alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p (suc z) xs)))
    (hq : Nonempty (Derivation body Delta (programGraph q (suc z) xs))) :
    Nonempty (Derivation body Delta (programGraph (both p q) (suc z) xs)) :=
  conjunctionAccept p q xs hp hq

theorem sameTag (xs : Fin 19 → OT alpha) (tag : Nat)
    (hx : Nonempty (Derivation body Delta (eqn (xs 0) (numeral tag))))
    (hy : Nonempty (Derivation body Delta (eqn (xs 7) (numeral tag)))) :
    Nonempty (Derivation body Delta (programGraph (eqField 0 7) (suc z) xs)) := by
  obtain ⟨hx⟩ := hx
  obtain ⟨hy⟩ := hy
  exact eqAccept 0 7 xs ⟨trans hx (symm hy)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.InternalSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.InternalSupportProof
