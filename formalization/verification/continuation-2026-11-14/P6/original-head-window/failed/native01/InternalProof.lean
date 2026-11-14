module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadWindow.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadResult.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadWindow.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalOriginalUniformVertexPathSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalConstructorSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem chooseFactor (actual : Nat) (raw symbols types out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph (leftOf (.projection 0))
      (numeral actual) ![raw,symbols,types]))) (k : Nat) (yes no : Program 3) :
    Nonempty (Derivation body Delta (graph3 (choose k yes no) out raw symbols types)) ↔
    Nonempty (Derivation body Delta (graph3 (if actual = k then yes else no) out raw symbols types)) :=
  ⟨branchNumeralElim actual k (leftOf (.projection 0)) no yes out ![raw,symbols,types] ht,
   branchNumeralIntro actual k (leftOf (.projection 0)) no yes out ![raw,symbols,types] ht⟩

theorem dispatch (n : Nat) (arity : Fin n → Nat) (tag : Fin 6) (raw symbols types out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph (leftOf (.projection 0))
      (numeral tag.val) ![raw,symbols,types]))) :
    Nonempty (Derivation body Delta (graph3 (window n arity) out raw symbols types)) ↔
    Nonempty (Derivation body Delta (graph3 (atPayload n arity tag.val) out raw symbols types)) := by
  fin_cases tag <;> simp [window,chooseFactor _ raw symbols types out ht]

theorem internalBranch : Targets.InternalBranch := by
  intro n arity body alpha Delta tag raw payload symbols types out hp
  obtain ⟨hi⟩ := InternalRecursionClosureLogicProof.closedApply
    (InternalUnpairProof.actualOriginalGeneratedCodeInverse body alpha raw (numeral tag.val) payload) hp
  let xs : Fin 3 → OTerm alpha := ![raw,symbols,types]
  have ht : Nonempty (Derivation body Delta (programGraph (leftOf (.projection 0)) (numeral tag.val) xs)) :=
    unaryValue InternalUnpair.left (.projection 0) (numeral tag.val) raw xs
      ⟨Derivation.conjunctionLeft hi⟩ (projectionValue 0 xs)
  have hr : Nonempty (Derivation body Delta (programGraph (rightOf (.projection 0)) payload xs)) :=
    unaryValue InternalUnpair.right (.projection 0) payload raw xs
      ⟨Derivation.conjunctionRight hi⟩ (projectionValue 0 xs)
  have hd := dispatch n arity tag raw symbols types out ht
  constructor
  · intro h
    exact ternaryRecover (branchWindow n arity tag.val) (rightOf (.projection 0)) (.projection 1) (.projection 2)
      out payload symbols types xs (hd.mp h) hr (projectionValue 1 xs) (projectionValue 2 xs)
  · intro h
    exact hd.mpr (ternaryValue (branchWindow n arity tag.val) (rightOf (.projection 0)) (.projection 1) (.projection 2)
      out payload symbols types xs h hr (projectionValue 1 xs) (projectionValue 2 xs))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadWindow.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadWindow.InternalProof
