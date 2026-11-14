module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadClass.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentTagFields.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
public import Mathlib.Tactic.FinCases
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.InternalSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadClass.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalConstructorSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InternalGraphCompositionFunctionalityProof
open OriginalRawSyntaxTransport (constant)
open InternalTagArithmeticSyntaxProof (eqn)
theorem constantTransfer (raw payload out : OTerm alpha) :
    Nonempty (Derivation body Delta (graph1 (constant 1 0) out raw)) ↔
    Nonempty (Derivation body Delta (graph1 (constant 1 0) out payload)) := by
  constructor
  · intro h
    have he := valueUnique (constant 1 0) (numeral 0) out ![raw] (constantValue 0 ![raw]) h
    exact outputTransport (constant 1 0) (numeral 0) out ![payload] he (constantValue 0 ![payload])
  · intro h
    have he := valueUnique (constant 1 0) (numeral 0) out ![payload] (constantValue 0 ![payload]) h
    exact outputTransport (constant 1 0) (numeral 0) out ![raw] he (constantValue 0 ![raw])

theorem chooseFactor (actual : Nat) (raw out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left (numeral actual) raw)))
    (k : Nat) (yes no : Program 1) :
    Nonempty (Derivation body Delta (graph1 (OriginalHeadEncodingBridge.choose k yes no) out raw)) ↔
    Nonempty (Derivation body Delta (graph1 (if actual = k then yes else no) out raw)) :=
  ⟨branchNumeralElim actual k InternalUnpair.left no yes out ![raw] ht,
    branchNumeralIntro actual k InternalUnpair.left no yes out ![raw] ht⟩

theorem internalTagFactor : Targets.InternalTagFactor := by
  intro body alpha Delta tag raw payload out hp
  obtain ⟨hi⟩ := InternalRecursionClosureLogicProof.closedApply
    (InternalUnpairProof.actualOriginalGeneratedCodeInverse body alpha raw (numeral tag.val) payload) hp
  have ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left (numeral tag.val) raw)) :=
    ⟨Derivation.conjunctionLeft hi⟩
  have hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload raw)) :=
    ⟨Derivation.conjunctionRight hi⟩
  have comp (k : Nat) :
      Nonempty (Derivation body Delta (graph1 (atPayload k) out raw)) ↔
      Nonempty (Derivation body Delta (graph1 (branchClass k) out payload)) :=
    ⟨fun h => unaryRecover (branchClass k) InternalUnpair.right out payload ![raw] h hr,
      fun h => unaryValue (branchClass k) InternalUnpair.right out payload ![raw] h hr⟩
  fin_cases tag <;> simp only [headClass,chooseFactor _ raw out ht] <;> simp only [ite_true,ite_false,
    show (0:Nat) ≠ 4 by decide,show (0:Nat) ≠ 5 by decide,
    show (1:Nat) ≠ 4 by decide,show (1:Nat) ≠ 5 by decide,
    show (2:Nat) ≠ 4 by decide,show (2:Nat) ≠ 5 by decide,
    show (3:Nat) ≠ 4 by decide,show (3:Nat) ≠ 5 by decide,show (5:Nat) ≠ 4 by decide]
  · exact constantTransfer raw payload out
  · exact constantTransfer raw payload out
  · exact constantTransfer raw payload out
  · exact constantTransfer raw payload out
  · exact comp 4
  · exact comp 5

theorem internalEquivalence : Targets.InternalEquivalence := by
  intro body alpha Delta rawF rawG classF classG hf hg
  let xs : Fin 2 → OTerm alpha := ![rawF,rawG]
  have hl : Nonempty (Derivation body Delta (programGraph leftClass classF xs)) :=
    unaryValue headClass (.projection 0) classF rawF xs hf (projectionValue 0 xs)
  have hr : Nonempty (Derivation body Delta (programGraph rightClass classG xs)) :=
    unaryValue headClass (.projection 1) classG rawG xs hg (projectionValue 1 xs)
  constructor
  · intro h
    exact InternalEqualityTestProof.equalityOfAcceptance classF classG
      (binaryRecover InternalEqualityTest.equalityTest leftClass rightClass (numeral 1) classF classG xs h hl hr)
  · intro h
    exact binaryValue InternalEqualityTest.equalityTest leftClass rightClass (numeral 1) classF classG xs
      (InternalEqualityTestCompositionProof.equalityOfEqual classF classG h) hl hr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadClass.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadClass.InternalProof
