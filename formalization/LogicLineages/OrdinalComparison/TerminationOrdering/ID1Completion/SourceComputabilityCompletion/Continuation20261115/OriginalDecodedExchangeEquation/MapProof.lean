module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.CoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.CoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntryCount.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.MapProof
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

open InductionDefinitions InductionSyntaxProof BindingProof
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (eqnRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalListCodecDecompositionSupportProof
open InternalQuotientComparisonProof InternalBetaTotalityProof

open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open AgreementDefinitions AgreementSyntaxProof
variable (E : Program 2)
theorem rawStep (raw : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw E raw))) :
    Nonempty (Derivation body Delta (AtRaw E raw)) := by
  apply atRawIntro E raw
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  let r : OTerm (alpha ⊕ Fin 3) := raw.relabel Sum.inl
  let left : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
  let right : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
  let out : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
  let Theta := fields E r left right out :: Delta.map (fun q => q.relabel Sum.inl)
  change Derivation body Theta (result E r left right out)
  have hf : Nonempty (Derivation body Theta (fields E r left right out)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih (Sum.inl : alpha → alpha ⊕ Fin 3) Theta (by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  rw [belowRawRename E] at ihj
  exact Classical.choice (CoreProof.core E r left right out ihj (andLeft hf) (andRight hf))

theorem transport (keys left right out : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (lookupAgreement E keys left right)))
    (hv : Nonempty (Derivation body Delta (graph2 (MapDefinitions.orderedMap E) out keys left))) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph out keys right)) :=
  atRawApply E keys left right out (rawInduction E keys (fun _ _ r h => rawStep E r h)) (andIntro ha hv)

theorem reverseTransport (keys left right out : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (lookupAgreement E keys left right)))
    (hv : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph out keys right))) :
    Nonempty (Derivation body Delta (graph2 (MapDefinitions.orderedMap E) out keys left)) := by
  apply programCases (MapDefinitions.orderedMap E) (Fin.cons keys (Fin.cons left Fin.elim0)) _
  intro beta j Theta actual hj hx
  simp only [consTermRename,emptyRename] at hx
  rw [graph2Rename]
  have haj := InternalGraphCompositionFunctionalityProof.renameInto ha j Theta hj
  rw [agreementRename E] at haj
  have hvj := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
  rw [graph2Rename] at hvj
  have hm := transport E (keys.relabel j) (left.relabel j) (right.relabel j) actual haj hx
  have he := valueUnique ExchangeMapGraph.mapGraph actual (out.relabel j)
    ![keys.relabel j,right.relabel j] hm hvj
  exact outputTransport (MapDefinitions.orderedMap E) actual (out.relabel j)
    ![keys.relabel j,left.relabel j] he hx

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.MapProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.MapProof
