module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.PositiveProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.ZeroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.MetadataProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.InductionTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.RankStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open OriginalRawSyntaxTransportInternalConstructorFieldsProof OriginalRawSyntaxTransportInternalConstructorSelectorsProof
open InternalQuotientComparisonProof (orLeft orRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open OriginalEnumerationRecursionInterface
open InternalAcceptanceSupportProof
open Lists ListSyntaxProof InductionSyntaxProof InductionBindingProof
open InternalPositiveUnfoldingSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
theorem zeroAtRank (n : Nat) (node param out : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 R z node param)))
    (he : Nonempty (Derivation body Delta (graph2 (OriginalEnumerationRecursion.enumeration n) out node param))) :
    Nonempty (Derivation body Delta (AllValid n out)) := by
  apply MetadataProof.cases node param z _ hr
  intro beta j Theta ys hj hn hp h2 h3
  rw [allRename]
  simp only [InternalTagArithmeticSyntaxProof.zRelabel] at hn
  have hej := renameInto he j Theta hj
  rw [graph2Rename] at hej
  exact ZeroProof.atKnown n (node.relabel j) (param.relabel j) (ys 0) (out.relabel j) hn hej

theorem positiveAtRank (n : Nat) (node param fuel out : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRank n (suc fuel))))
    (hr : Nonempty (Derivation body Delta (graph2 R (suc fuel) node param)))
    (he : Nonempty (Derivation body Delta (graph2 (OriginalEnumerationRecursion.enumeration n) out node param))) :
    Nonempty (Derivation body Delta (AllValid n out)) := by
  apply MetadataProof.cases node param (suc fuel) _ hr
  intro beta j Theta ys hj hn hp h2 h3
  rw [allRename]
  simp only [InternalTagArithmeticSyntaxProof.sucRelabel] at hn
  have ihj := renameInto ih j Theta hj
  simp only [belowRankRename,InternalTagArithmeticSyntaxProof.sucRelabel] at ihj
  have hej := renameInto he j Theta hj
  rw [graph2Rename] at hej
  exact PositiveProof.atKnown n (node.relabel j) (param.relabel j) (ys 0) (fuel.relabel j)
    (ys 1) (ys 3) (ys 5) (ys 6) (ys 2) (ys 4) (out.relabel j) ihj hn hp h2 h3 hej

theorem atEnumeration (n : Nat) (node param fuel out : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRank n fuel)))
    (hr : Nonempty (Derivation body Delta (graph2 R fuel node param)))
    (he : Nonempty (Derivation body Delta (graph2 (OriginalEnumerationRecursion.enumeration n) out node param))) :
    Nonempty (Derivation body Delta (AllValid n out)) := by
  apply zeroSuccessorCases Delta fuel _
  · have hz : Nonempty (Derivation body (eqn fuel z :: Delta) (eqn fuel z)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact zeroAtRank n node param out
      (outputTransport R fuel z ![node,param] hz (withHyp hr (eqn fuel z))) (withHyp he (eqn fuel z))
  · intro beta j Theta pred hj hf
    rw [allRename]
    have ihj := renameInto ih j Theta hj
    rw [belowRankRename] at ihj
    have hrj := renameInto hr j Theta hj
    have hej := renameInto he j Theta hj
    rw [graph2Rename] at hrj hej
    exact positiveAtRank n (node.relabel j) (param.relabel j) pred (out.relabel j)
      (InductionTransportProof.belowTransport n (fuel.relabel j) (suc pred) hf ihj)
      (outputTransport R (fuel.relabel j) (suc pred) ![node.relabel j,param.relabel j] hf hrj) hej

theorem step (n : Nat) (r : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRank n r))) :
    Nonempty (Derivation body Delta (AtRank n r)) := by
  apply atRankIntro n r
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  let key : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
  let param : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
  let out : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
  let row := graph2 R (r.relabel Sum.inl) key param ⊓ graph2 (OriginalEnumerationRecursion.enumeration n) out key param
  let Theta := row :: Delta.map (fun q => q.relabel Sum.inl)
  have hj : ∀ q ∈ Delta, q.relabel (Sum.inl : alpha → alpha ⊕ Fin 3) ∈ Theta := by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have ihj := renameInto ih (Sum.inl : alpha → alpha ⊕ Fin 3) Theta hj
  rw [belowRankRename] at ihj
  have hf : Nonempty (Derivation body Theta row) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact Classical.choice (atEnumeration n key param (r.relabel Sum.inl) out ihj (andLeft hf) (andRight hf))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.RankStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.RankStepProof
