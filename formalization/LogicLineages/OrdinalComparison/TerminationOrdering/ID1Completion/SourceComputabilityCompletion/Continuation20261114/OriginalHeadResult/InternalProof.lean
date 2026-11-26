module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadResult.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentTagFields.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
public import Mathlib.Tactic.FinCases
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadResult.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalConstructorSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem chooseFactor (actual : Nat) (raw out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left (numeral actual) raw)))
    (k : Nat) (yes no : Program 1) :
    Nonempty (Derivation body Delta (graph1 (OriginalHeadEncodingBridge.choose k yes no) out raw)) ↔
    Nonempty (Derivation body Delta (graph1 (if actual = k then yes else no) out raw)) :=
  ⟨branchNumeralElim actual k InternalUnpair.left no yes out ![raw] ht,
    branchNumeralIntro actual k InternalUnpair.left no yes out ![raw] ht⟩

theorem dispatch (tag : Fin 6) (raw out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left (numeral tag.val) raw))) :
    Nonempty (Derivation body Delta (graph1 headResult out raw)) ↔
    Nonempty (Derivation body Delta (graph1 (atPayload tag.val) out raw)) := by
  fin_cases tag <;> simp [headResult,chooseFactor _ raw out ht]

theorem internalTagFactor : Targets.InternalTagFactor := by
  intro body alpha Delta tag raw payload out hp
  obtain ⟨hi⟩ := InternalRecursionClosureLogicProof.closedApply
    (InternalUnpairProof.actualOriginalGeneratedCodeInverse body alpha raw (numeral tag.val) payload) hp
  have hd := dispatch tag raw out ⟨Derivation.conjunctionLeft hi⟩
  constructor
  · intro h
    exact unaryRecover (branchResult tag.val) InternalUnpair.right out payload ![raw]
      (hd.mp h) ⟨Derivation.conjunctionRight hi⟩
  · intro h
    exact hd.mpr (unaryValue (branchResult tag.val) InternalUnpair.right out payload ![raw]
      h ⟨Derivation.conjunctionRight hi⟩)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadResult.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadResult.InternalProof
