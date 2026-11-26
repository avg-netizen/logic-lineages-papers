module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedCacheDomain.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentExchangeLayer.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedCacheDomain.LayerProof
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
theorem unequalZero (out inner : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn out (suc inner)))) :
    Nonempty (Derivation body Delta (eqn out z).not) := by
  obtain ⟨hew⟩ := withHyp he (eqn out z)
  exact ⟨Derivation.implicationIntroduction
    (sucNeZeroApply (trans (symm hew) (Derivation.hypothesis List.mem_cons_self)))⟩

theorem positiveAt (U : Fin 19 → Program 3) (V : Program 3)
    (node answers param out control inner : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph3 V (suc control) node answers param)))
    (hi : Nonempty (Derivation body Delta (graph3 (TransparentExchangeLayer.body U) inner node answers param)))
    (ho : Nonempty (Derivation body Delta (graph3 (TransparentExchangeLayer.optional U V) out node answers param))) :
    Nonempty (Derivation body Delta (eqn out z).not) := by
  have hs := unaryValue .succ (TransparentExchangeLayer.body U) (suc inner) inner ![node,answers,param]
    (successorValue (Fin.cons inner Fin.elim0)) hi
  have hn := successorBranchIntro V (InternalLessThan.constantOne 3) _ (suc inner) control ![node,answers,param] hv hs
  exact unequalZero out inner (valueUnique (TransparentExchangeLayer.optional U V) out (suc inner) ![node,answers,param] ho hn)

theorem positive (U : Fin 19 → Program 3) (V : Program 3)
    (node answers param out control : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph3 V (suc control) node answers param)))
    (ho : Nonempty (Derivation body Delta (graph3 (TransparentExchangeLayer.optional U V) out node answers param))) :
    Nonempty (Derivation body Delta (eqn out z).not) := by
  apply programCases (TransparentExchangeLayer.body U) (Fin.cons node (Fin.cons answers (Fin.cons param Fin.elim0))) _
  intro beta j Theta inner hj hi
  simp only [consTermRename,emptyRename] at hi
  simp only [eqnRelabel,zRelabel]
  have hvj := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
  simp only [graph3Rename,sucRelabel] at hvj
  have hoj := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
  rw [graph3Rename] at hoj
  exact positiveAt U V (node.relabel j) (answers.relabel j) (param.relabel j) (out.relabel j) (control.relabel j) inner hvj hi hoj

theorem atControl (U : Fin 19 → Program 3) (V : Program 3)
    (node answers param out control : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph3 V control node answers param)))
    (ho : Nonempty (Derivation body Delta (graph3 (TransparentExchangeLayer.optional U V) out node answers param))) :
    Nonempty (Derivation body Delta (eqn out z).not) := by
  apply zeroSuccessorCases Delta control _
  · have hv0 := outputTransport V control z ![node,answers,param]
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hv (eqn control z))
    have hn := zeroBranchIntro V (InternalLessThan.constantOne 3) _ (suc z) ![node,answers,param] hv0
      (constantOneValue ![node,answers,param])
    exact unequalZero out z (valueUnique (TransparentExchangeLayer.optional U V) out (suc z) ![node,answers,param]
      (withHyp ho (eqn control z)) hn)
  · intro beta j Theta k hj he
    simp only [eqnRelabel,zRelabel]
    have hvj := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
    rw [graph3Rename] at hvj
    have hoj := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
    rw [graph3Rename] at hoj
    exact positive U V (node.relabel j) (answers.relabel j) (param.relabel j) (out.relabel j) k
      (outputTransport V (control.relabel j) (suc k) ![node.relabel j,answers.relabel j,param.relabel j] he hvj) hoj

theorem optionalNonzero (U : Fin 19 → Program 3) (V : Program 3)
    (node answers param out : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (graph3 (TransparentExchangeLayer.optional U V) out node answers param))) :
    Nonempty (Derivation body Delta (eqn out z).not) := by
  apply programCases V (Fin.cons node (Fin.cons answers (Fin.cons param Fin.elim0))) _
  intro beta j Theta control hj hv
  simp only [consTermRename,emptyRename] at hv
  simp only [eqnRelabel,zRelabel]
  have hoj := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
  rw [graph3Rename] at hoj
  exact atControl U V (node.relabel j) (answers.relabel j) (param.relabel j) (out.relabel j) control hv hoj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedCacheDomain.LayerProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedCacheDomain.LayerProof
