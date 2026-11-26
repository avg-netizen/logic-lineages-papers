module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.RebuildCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.CoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntryCount.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendRunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.CountAgreementBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.RebuildProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open RebuildInductionDefinitions RebuildInductionSyntaxProof RebuildBindingProof
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (eqnRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalListCodecDecompositionSupportProof
open InternalQuotientComparisonProof InternalBetaTotalityProof

open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open CountAgreement CountAgreementSyntaxProof CountAgreementBindingProof
theorem rawStep (raw : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw))) :
    Nonempty (Derivation body Delta (AtRaw raw)) := by
  apply atRawIntro raw
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  let r : OTerm (alpha ⊕ Fin 2) := raw.relabel Sum.inl
  let left : OTerm (alpha ⊕ Fin 2) := .var (.inr 0)
  let right : OTerm (alpha ⊕ Fin 2) := .var (.inr 1)
  let Theta := RebuildInductionDefinitions.fields r left right :: Delta.map (fun q => q.relabel Sum.inl)
  change Derivation body Theta (result r left right)
  have hf : Nonempty (Derivation body Theta (RebuildInductionDefinitions.fields r left right)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ihj := renameInto ih (Sum.inl : alpha → alpha ⊕ Fin 2) Theta (by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  rw [RebuildInductionSyntaxProof.belowRawRename] at ihj
  exact Classical.choice (RebuildCoreProof.core r left right hf ihj)

theorem allCounts (raw left right : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (agreement left right))) :
    Nonempty (Derivation body Delta (graph3 ArgumentCountComparison.allCounts (numeral 1) raw left right)) :=
  atRawApply raw left right (rawInduction raw (fun _ _ r h => rawStep r h)) ha

theorem permutation (left right : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (agreement left right))) :
    Nonempty (Derivation body Delta (graph2 ArgumentCountComparison.permutation (numeral 1) left right)) := by
  apply programCases InternalApplicationValidityStackAppend.append (Fin.cons left (Fin.cons right Fin.elim0)) _
  intro beta j Theta joined hj hjoin
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  simp only [consTermRename,emptyRename] at hjoin
  have haj := renameInto ha j Theta hj
  rw [agreementRename] at haj
  let xs : Fin 2 → OTerm beta := Fin.cons (left.relabel j) (Fin.cons (right.relabel j) Fin.elim0)
  exact InternalOriginalUniformVertexPathSupportProof.ternaryValue ArgumentCountComparison.allCounts
    InternalApplicationValidityStackAppend.append (.projection 0) (.projection 1) (numeral 1) joined (left.relabel j) (right.relabel j) xs
    (allCounts joined (left.relabel j) (right.relabel j) haj) hjoin (projectionValue 0 xs) (projectionValue 1 xs)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.RebuildProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.RebuildProof
