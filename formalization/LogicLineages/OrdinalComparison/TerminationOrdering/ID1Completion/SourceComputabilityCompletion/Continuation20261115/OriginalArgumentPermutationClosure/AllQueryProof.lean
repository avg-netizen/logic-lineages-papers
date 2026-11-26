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
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.AllQueryProof
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
theorem absentLeft (left right joined needle : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined left right)))
    (hn : Nonempty (Derivation body Delta (graph2 contains (numeral 1) joined needle).not)) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) left needle).not) := by
  let A := graph2 contains (numeral 1) left needle
  have hh := PrimaryExpansion.PreservationProof.appendPreservation left right joined needle
    (withHyp ha A) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hh⟩ := hh
  obtain ⟨hn⟩ := hn
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination (InternalBetaTotalityProof.addHyp hn _) hh)⟩

theorem absentRight (left right joined needle : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined left right)))
    (hn : Nonempty (Derivation body Delta (graph2 contains (numeral 1) joined needle).not)) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) right needle).not) := by
  let A := graph2 contains (numeral 1) right needle
  have hh := PrimaryEdgeInclusion.AppendRightProof.appendPreservation left right joined needle
    (withHyp ha A) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hh⟩ := hh
  obtain ⟨hn⟩ := hn
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination (InternalBetaTotalityProof.addHyp hn _) hh)⟩

theorem everyQuery (left right joined needle lc rc : OTerm alpha)
    (hjoin : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined left right)))
    (ha : Nonempty (Derivation body Delta (graph3 ArgumentCountComparison.allCounts (numeral 1) joined left right)))
    (hl : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count lc left needle)))
    (hr : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count rc right needle))) :
    Nonempty (Derivation body Delta (eqn lc rc)) := by
  apply formulaCases (graph2 contains (numeral 1) joined needle)
  · exact SupportedProof.supportedCounts joined left right needle lc rc (withHyp ha _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hl _) (withHyp hr _)
  · have hn : Nonempty (Derivation body ((graph2 contains (numeral 1) joined needle).not :: Delta)
      (graph2 contains (numeral 1) joined needle).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hzl⟩ := AbsentProof.absentCount left needle lc (absentLeft left right joined needle (withHyp hjoin _) hn) (withHyp hl _)
    obtain ⟨hzr⟩ := AbsentProof.absentCount right needle rc (absentRight left right joined needle (withHyp hjoin _) hn) (withHyp hr _)
    exact ⟨trans hzl (symm hzr)⟩

theorem atAppend (left right joined : OTerm alpha)
    (hjoin : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined left right)))
    (ha : Nonempty (Derivation body Delta (graph3 ArgumentCountComparison.allCounts (numeral 1) joined left right))) :
    Nonempty (Derivation body Delta (agreement left right)) := by
  apply agreementIntro left right
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  let l := left.relabel (Sum.inl : alpha → alpha ⊕ Fin 3)
  let r := right.relabel (Sum.inl : alpha → alpha ⊕ Fin 3)
  let needle : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
  let lc : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
  let rc : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
  let Theta := fields l r needle lc rc :: Delta.map (fun q => q.relabel Sum.inl)
  change Derivation body Theta (eqn lc rc)
  have hf : Nonempty (Derivation body Theta (fields l r needle lc rc)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hj : ∀ q ∈ Delta, q.relabel (Sum.inl : alpha → alpha ⊕ Fin 3) ∈ Theta := by
    intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have hjoinj := renameInto hjoin Sum.inl Theta hj
  have haj := renameInto ha Sum.inl Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hjoinj haj
  exact Classical.choice (everyQuery l r (joined.relabel Sum.inl) needle lc rc hjoinj haj (andLeft hf) (andRight hf))

theorem permutationAgreement (left right : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 ArgumentCountComparison.permutation (numeral 1) left right))) :
    Nonempty (Derivation body Delta (agreement left right)) := by
  apply programCases InternalApplicationValidityStackAppend.append (Fin.cons left (Fin.cons right Fin.elim0)) _
  intro beta j Theta joined hj hjoin
  rw [agreementRename]
  simp only [consTermRename,emptyRename] at hjoin
  have haj := renameInto ha j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at haj
  let xs : Fin 2 → OTerm beta := Fin.cons (left.relabel j) (Fin.cons (right.relabel j) Fin.elim0)
  have hc := InternalOriginalUniformVertexPathSupportProof.ternaryRecover ArgumentCountComparison.allCounts
    InternalApplicationValidityStackAppend.append (.projection 0) (.projection 1)
    (numeral 1) joined (left.relabel j) (right.relabel j) xs haj hjoin (projectionValue 0 xs) (projectionValue 1 xs)
  exact atAppend (left.relabel j) (right.relabel j) joined hjoin hc

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.AllQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.AllQueryProof
