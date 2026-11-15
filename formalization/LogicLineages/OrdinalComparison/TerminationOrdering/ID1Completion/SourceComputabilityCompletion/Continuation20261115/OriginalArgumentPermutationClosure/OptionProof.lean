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
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalArgumentPermutation.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.OptionProof
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
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
theorem leftNonzero (base target value : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract value base (numeral 0))))
    (ha : Nonempty (Derivation body Delta (graph2 OriginalArgumentPermutation.check (numeral 1) base target))) :
    Nonempty (Derivation body Delta (eqn value z).not) := by
  have he : Nonempty (Derivation body (eqn value z :: Delta) (eqn value z)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hv0 := outputTransport ArgumentEntriesRecursor.extract value z ![base,numeral 0] he (withHyp hv _)
  have hz := (OriginalArgumentPermutation.InternalProof.internalNone body alpha (eqn value z :: Delta) base target).1 hv0
  obtain ⟨heq⟩ := valueUnique OriginalArgumentPermutation.check (numeral 1) z ![base,target] (withHyp ha _) hz
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply heq)⟩

theorem rightNonzero (base target list value : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc list) base (numeral 0))))
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract value target (numeral 0))))
    (ha : Nonempty (Derivation body Delta (graph2 OriginalArgumentPermutation.check (numeral 1) base target))) :
    Nonempty (Derivation body Delta (eqn value z).not) := by
  have he : Nonempty (Derivation body (eqn value z :: Delta) (eqn value z)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hv0 := outputTransport ArgumentEntriesRecursor.extract value z ![target,numeral 0] he (withHyp hv _)
  have hz := (OriginalArgumentPermutation.InternalProof.internalNone body alpha (eqn value z :: Delta) base target).2 list (withHyp hs _) hv0
  obtain ⟨heq⟩ := valueUnique OriginalArgumentPermutation.check (numeral 1) z ![base,target] (withHyp ha _) hz
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply heq)⟩

theorem someValueCases (raw value : OTerm alpha) (psi : Formula alpha)
    (hv : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract value raw (numeral 0))))
    (hn : Nonempty (Derivation body Delta (eqn value z).not))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (list : OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 ArgumentEntriesRecursor.extract (suc list) (raw.relabel j) (numeral 0))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply zeroSuccessorCases Delta value psi
  · obtain ⟨hn⟩ := hn
    exact ⟨Derivation.explosion (Derivation.implicationElimination (InternalBetaTotalityProof.addHyp hn _) (Derivation.hypothesis List.mem_cons_self))⟩
  · intro beta j Theta list hj he
    have hvj := renameInto hv j Theta hj
    simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hvj
    exact next beta j Theta list hj (outputTransport ArgumentEntriesRecursor.extract (value.relabel j) (suc list)
      ![raw.relabel j,numeral 0] he hvj)

theorem leftCases (base target : OTerm alpha) (psi : Formula alpha)
    (ha : Nonempty (Derivation body Delta (graph2 OriginalArgumentPermutation.check (numeral 1) base target)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (out : OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 ArgumentEntriesRecursor.extract (suc out) (base.relabel j) (numeral 0))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply programCases ArgumentEntriesRecursor.extract (Fin.cons base (Fin.cons (numeral 0) Fin.elim0)) psi
  intro beta j Theta value hj hv
  simp only [consTermRename,emptyRename,GuardedSourceSyntaxProof.numeralRename] at hv
  have haj := renameInto ha j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at haj
  apply someValueCases (base.relabel j) value (psi.relabel j) hv (leftNonzero (base.relabel j) (target.relabel j) value hv haj)
  intro gamma k Xi out hk ho
  have hnext := next gamma (k ∘ j) Xi out
    (by intro q hq; simpa only [← formulaRelabelComposition] using hk _ (hj q hq))
    (by simpa only [Term.relabel_relabel] using ho)
  simpa only [formulaRelabelComposition] using hnext

theorem rightCases (base target list : OTerm alpha) (psi : Formula alpha)
    (hs : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc list) base (numeral 0))))
    (ha : Nonempty (Derivation body Delta (graph2 OriginalArgumentPermutation.check (numeral 1) base target)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (out : OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 ArgumentEntriesRecursor.extract (suc out) (target.relabel j) (numeral 0))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply programCases ArgumentEntriesRecursor.extract (Fin.cons target (Fin.cons (numeral 0) Fin.elim0)) psi
  intro beta j Theta value hj hv
  simp only [consTermRename,emptyRename,GuardedSourceSyntaxProof.numeralRename] at hv
  have haj := renameInto ha j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at haj
  have hsj := renameInto hs j Theta hj
  simp only [graph2Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hsj
  apply someValueCases (target.relabel j) value (psi.relabel j) hv (rightNonzero (base.relabel j) (target.relabel j) (list.relabel j) value hsj hv haj)
  intro gamma k Xi out hk ho
  have hnext := next gamma (k ∘ j) Xi out
    (by intro q hq; simpa only [← formulaRelabelComposition] using hk _ (hj q hq))
    (by simpa only [Term.relabel_relabel] using ho)
  simpa only [formulaRelabelComposition] using hnext

theorem bothCases (base target : OTerm alpha) (psi : Formula alpha)
    (ha : Nonempty (Derivation body Delta (graph2 OriginalArgumentPermutation.check (numeral 1) base target)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (left right : OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 ArgumentEntriesRecursor.extract (suc left) (base.relabel j) (numeral 0))) →
      Nonempty (Derivation body Theta (graph2 ArgumentEntriesRecursor.extract (suc right) (target.relabel j) (numeral 0))) →
      Nonempty (Derivation body Theta (graph2 ArgumentCountComparison.permutation (numeral 1) left right)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply leftCases base target psi ha
  intro beta j Theta left hj hl
  have haj := renameInto ha j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at haj
  apply rightCases (base.relabel j) (target.relabel j) left (psi.relabel j) hl haj
  intro gamma k Xi right hk hr
  have hajk := renameInto haj k Xi hk
  have hljk := renameInto hl k Xi hk
  simp only [graph2Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hajk hljk
  have hp := (OriginalArgumentPermutation.InternalProof.internalSome body gamma Xi ((base.relabel j).relabel k)
    ((target.relabel j).relabel k) (left.relabel k) right (numeral 1) hljk hr).mp hajk
  have hnext := next gamma (k ∘ j) Xi (left.relabel k) right
    (by intro q hq; simpa only [← formulaRelabelComposition] using hk _ (hj q hq))
    (by simpa only [Term.relabel_relabel] using hljk)
    (by simpa only [Term.relabel_relabel] using hr) hp
  simpa only [formulaRelabelComposition] using hnext

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.OptionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.OptionProof
