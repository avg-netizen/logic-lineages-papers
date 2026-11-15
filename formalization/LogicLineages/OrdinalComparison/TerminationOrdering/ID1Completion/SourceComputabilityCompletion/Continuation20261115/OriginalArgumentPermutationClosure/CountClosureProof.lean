module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.CountAgreementBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.CoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntryCount.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMembership.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendRunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.AbsentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.SupportedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.PreservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.AppendRightProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.AllQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.RebuildProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.CountClosureProof
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

open CountAgreement CountAgreementSyntaxProof CountAgreementBindingProof
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (eqnRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalListCodecDecompositionSupportProof
open InternalQuotientComparisonProof InternalBetaTotalityProof

open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
theorem transAtCounts (left middle right needle lc rc : OTerm alpha)
    (hab : Nonempty (Derivation body Delta (agreement left middle)))
    (hbc : Nonempty (Derivation body Delta (agreement middle right)))
    (hl : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count lc left needle)))
    (hr : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count rc right needle))) :
    Nonempty (Derivation body Delta (eqn lc rc)) := by
  apply programCases ArgumentEntryCount.count (Fin.cons middle (Fin.cons needle Fin.elim0)) _
  intro beta j Theta mc hj hm
  rw [eqnRelabel]
  simp only [consTermRename,emptyRename] at hm
  have habj := renameInto hab j Theta hj
  have hbcj := renameInto hbc j Theta hj
  have hlj := renameInto hl j Theta hj
  have hrj := renameInto hr j Theta hj
  simp only [agreementRename,graph2Rename] at habj hbcj hlj hrj
  obtain ⟨he1⟩ := agreementApply (left.relabel j) (middle.relabel j) (needle.relabel j) (lc.relabel j) mc habj hlj hm
  obtain ⟨he2⟩ := agreementApply (middle.relabel j) (right.relabel j) (needle.relabel j) mc (rc.relabel j) hbcj hm hrj
  exact ⟨trans he1 he2⟩

theorem symmetric (left right : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (agreement left right)))
    : Nonempty (Derivation body Delta (agreement right left)) := by
  apply agreementIntro right left
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  let leftJ := left.relabel (Sum.inl : alpha → alpha ⊕ Fin 3)
  let rightJ := right.relabel (Sum.inl : alpha → alpha ⊕ Fin 3)
  let needle : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
  let lc : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
  let rc : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
  let Theta := fields rightJ leftJ needle lc rc :: Delta.map (fun q => q.relabel Sum.inl)
  change Derivation body Theta (eqn lc rc)
  have hf : Nonempty (Derivation body Theta (fields rightJ leftJ needle lc rc)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hj : ∀ q ∈ Delta, q.relabel (Sum.inl : alpha → alpha ⊕ Fin 3) ∈ Theta := by
    intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have haj := renameInto ha Sum.inl Theta hj
  rw [agreementRename] at haj
  exact symm (Classical.choice (agreementApply leftJ rightJ needle rc lc haj (andRight hf) (andLeft hf)))

theorem transitive (left middle right : OTerm alpha)
    (hab : Nonempty (Derivation body Delta (agreement left middle)))
    (hbc : Nonempty (Derivation body Delta (agreement middle right)))
    : Nonempty (Derivation body Delta (agreement left right)) := by
  apply agreementIntro left right
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  let leftJ := left.relabel (Sum.inl : alpha → alpha ⊕ Fin 3)
  let middleJ := middle.relabel (Sum.inl : alpha → alpha ⊕ Fin 3)
  let rightJ := right.relabel (Sum.inl : alpha → alpha ⊕ Fin 3)
  let needle : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
  let lc : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
  let rc : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
  let Theta := fields leftJ rightJ needle lc rc :: Delta.map (fun q => q.relabel Sum.inl)
  change Derivation body Theta (eqn lc rc)
  have hf : Nonempty (Derivation body Theta (fields leftJ rightJ needle lc rc)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hj : ∀ q ∈ Delta, q.relabel (Sum.inl : alpha → alpha ⊕ Fin 3) ∈ Theta := by
    intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have habj := renameInto hab Sum.inl Theta hj
  rw [agreementRename] at habj
  have hbcj := renameInto hbc Sum.inl Theta hj
  rw [agreementRename] at hbcj
  exact Classical.choice (transAtCounts leftJ middleJ rightJ needle lc rc habj hbcj (andLeft hf) (andRight hf))

theorem permutationSymmetric (left right : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 ArgumentCountComparison.permutation (numeral 1) left right))) :
    Nonempty (Derivation body Delta (graph2 ArgumentCountComparison.permutation (numeral 1) right left)) :=
  RebuildProof.permutation right left (symmetric left right (AllQueryProof.permutationAgreement left right ha))

theorem permutationTransitive (left middle right : OTerm alpha)
    (hab : Nonempty (Derivation body Delta (graph2 ArgumentCountComparison.permutation (numeral 1) left middle)))
    (hbc : Nonempty (Derivation body Delta (graph2 ArgumentCountComparison.permutation (numeral 1) middle right))) :
    Nonempty (Derivation body Delta (graph2 ArgumentCountComparison.permutation (numeral 1) left right)) :=
  RebuildProof.permutation left right (transitive left middle right
    (AllQueryProof.permutationAgreement left middle hab) (AllQueryProof.permutationAgreement middle right hbc))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.CountClosureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.CountClosureProof
