module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBooleanRange.LayerRangeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentExchangeLayer.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBooleanRange.PayloadProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalGraphCompositionFunctionalityProof InternalTagArithmeticSupportProof
open InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel eqnRelabel)
open InternalRecursionGraphStepSyntaxProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open HeadWindowBooleanRange
open HeadWindowBooleanRange.InductionSyntaxProof (booleanRename)
theorem transport (out inner : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn out inner)))
    (hi : Nonempty (Derivation body Delta (BooleanValue inner))) :
    Nonempty (Derivation body Delta (BooleanValue out)) := by
  have h0 : Nonempty (Derivation body Delta ((eqn inner (numeral 0)).imp (BooleanValue out))) := by
    obtain ⟨he0⟩ := withHyp he (eqn inner (numeral 0))
    exact ⟨Derivation.implicationIntroduction (InternalQuotientComparisonProof.orLeft
      (trans he0 (Derivation.hypothesis List.mem_cons_self)))⟩
  have h1 : Nonempty (Derivation body Delta ((eqn inner (numeral 1)).imp (BooleanValue out))) := by
    obtain ⟨he1⟩ := withHyp he (eqn inner (numeral 1))
    exact ⟨Derivation.implicationIntroduction (InternalQuotientComparisonProof.orRight
      (trans he1 (Derivation.hypothesis List.mem_cons_self)))⟩
  obtain ⟨hi⟩ := hi
  obtain ⟨h0⟩ := h0
  obtain ⟨h1⟩ := h1
  exact ⟨InternalBetaTotalityProof.disjunctionElimination hi h0 h1⟩

theorem positiveAt (U : Fin 19 → Program 3) (V : Program 3)
    (node answers param out control inner : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph3 V (suc control) node answers param)))
    (hi : Nonempty (Derivation body Delta (graph3 (TransparentExchangeLayer.body U) inner node answers param)))
    (ho : Nonempty (Derivation body Delta (graph3 (TransparentExchangeLayer.optional U V) (suc out) node answers param))) :
    Nonempty (Derivation body Delta (BooleanValue out)) := by
  have hs := unaryValue .succ (TransparentExchangeLayer.body U) (suc inner) inner ![node,answers,param]
    (successorValue (Fin.cons inner Fin.elim0)) hi
  have hn := successorBranchIntro V (InternalLessThan.constantOne 3) _ (suc inner) control ![node,answers,param] hv hs
  obtain ⟨he⟩ := valueUnique (TransparentExchangeLayer.optional U V) (suc out) (suc inner) ![node,answers,param] ho hn
  exact transport out inner ⟨cancelSuc he⟩ (LayerRangeProof.bodyRange U body alpha Delta inner ![node,answers,param] hi)

theorem positive (U : Fin 19 → Program 3) (V : Program 3)
    (node answers param out control : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph3 V (suc control) node answers param)))
    (ho : Nonempty (Derivation body Delta (graph3 (TransparentExchangeLayer.optional U V) (suc out) node answers param))) :
    Nonempty (Derivation body Delta (BooleanValue out)) := by
  apply programCases (TransparentExchangeLayer.body U) (Fin.cons node (Fin.cons answers (Fin.cons param Fin.elim0))) _
  intro beta j Theta inner hj hi
  rw [booleanRename]
  simp only [consTermRename,emptyRename] at hi
  have hvj := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
  simp only [graph3Rename,sucRelabel] at hvj
  have hoj := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
  simp only [graph3Rename,sucRelabel] at hoj
  exact positiveAt U V (node.relabel j) (answers.relabel j) (param.relabel j) (out.relabel j) (control.relabel j) inner hvj hi hoj

theorem atControl (U : Fin 19 → Program 3) (V : Program 3)
    (node answers param out control : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph3 V control node answers param)))
    (ho : Nonempty (Derivation body Delta (graph3 (TransparentExchangeLayer.optional U V) (suc out) node answers param))) :
    Nonempty (Derivation body Delta (BooleanValue out)) := by
  apply zeroSuccessorCases Delta control _
  · have hv0 := outputTransport V control z ![node,answers,param]
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hv (eqn control z))
    have hn := zeroBranchIntro V (InternalLessThan.constantOne 3) (.composition .succ (fun _ : Fin 1 => TransparentExchangeLayer.body U)) (suc z) ![node,answers,param] hv0
      (InternalLessThanSupportProof.oneConstantValue ![node,answers,param])
    obtain ⟨he⟩ := valueUnique (TransparentExchangeLayer.optional U V) (suc out) (suc z) ![node,answers,param]
      (withHyp ho (eqn control z)) hn
    exact ⟨InternalQuotientComparisonProof.orLeft (cancelSuc he)⟩
  · intro beta j Theta k hj he
    rw [booleanRename]
    have hvj := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
    rw [graph3Rename] at hvj
    have hoj := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
    simp only [graph3Rename,sucRelabel] at hoj
    exact positive U V (node.relabel j) (answers.relabel j) (param.relabel j) (out.relabel j) k
      (outputTransport V (control.relabel j) (suc k) ![node.relabel j,answers.relabel j,param.relabel j] he hvj) hoj

theorem optionalPayload (U : Fin 19 → Program 3) (V : Program 3)
    (node answers param out : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (graph3 (TransparentExchangeLayer.optional U V) (suc out) node answers param))) :
    Nonempty (Derivation body Delta (BooleanValue out)) := by
  apply programCases V (Fin.cons node (Fin.cons answers (Fin.cons param Fin.elim0))) _
  intro beta j Theta control hj hv
  rw [booleanRename]
  simp only [consTermRename,emptyRename] at hv
  have hoj := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
  simp only [graph3Rename,sucRelabel] at hoj
  exact atControl U V (node.relabel j) (answers.relabel j) (param.relabel j) (out.relabel j) control hv hoj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBooleanRange.PayloadProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBooleanRange.PayloadProof
