module
public import LogicLineages.PersistentMarking.NumberedWindowInternalConsUnionReportBuildProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendSuffixProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendAgreementProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountEquivalenceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionProgressSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRawUnionFromEquivalentPartsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalConsUnionReportBuildProof (Report unionReportOfGraphs)
open NumberedWindowInternalDirectSourcePartitionRawTargets (ParsedTriplet)
open NumberedWindowInternalCertifiedUnionStepProof (unionGraph)
open NumberedWindowInternalCertifiedUnionProgressSupportProof (unionGraphRename)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalLiteralCountEquivalenceProof (exact_LiteralObserverTransitivity)
open NumberedWindowInternalLiteralCountAppendSuffixProof (exact_LiteralCommonSuffixCongruence)
open NumberedWindowInternalLiteralCountAppendAgreementProof (exact_LiteralCommonPrefixCongruence)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (keepThrough renameParser)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

abbrev App (l r u : OTerm α) : Formula α := programGraph append u ![l,r]
abbrev Cmp (l r : OTerm α) : Formula α := programGraph permutation (suc z) ![l,r]

private theorem renameCmp {β : Type} {Δ : List (Formula β)} (s t : OTerm α)
    (d : Nonempty (Derivation B Γ (Cmp s t))) (j : α → β)
    (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    Nonempty (Derivation B Δ (Cmp (s.relabel j) (t.relabel j))) := by
  simpa only [Cmp,sucRelabel,zRelabel] using renamePair permutation (suc z) s t d j keep

/-- Keep the actual destination's raw code fixed and replace either
component by a real equal-count scratch representative. Use this when
a non-changing side keeps its identical raw source term. -/
theorem exact_OriginalRawUnionFromEquivalentParts
    (a b u sa sb su oldL oldR oldJoined : OTerm α)
    (parsed : ParsedTriplet B Γ u a b su sa sb)
    (oldAppend : Nonempty (Derivation B Γ (App oldL oldR oldJoined)))
    (whole : Nonempty (Derivation B Γ (Cmp su oldJoined)))
    (left : Nonempty (Derivation B Γ (Cmp oldL sa)))
    (right : Nonempty (Derivation B Γ (Cmp oldR sb))) :
    Nonempty (Derivation B Γ (unionGraph permutation a b u)) := by
  apply programCases append ![sa,oldR] _
  intro β j Δ mid keep appMid
  rw [binaryInputsRename] at appMid
  rw [unionGraphRename]
  apply programCases append ![sa.relabel j,sb.relabel j] _
  intro γ k Ω newJoined held appNew
  rw [binaryInputsRename] at appNew
  rw [unionGraphRename]
  let ρ := k ∘ j
  have stay := keepThrough j k keep held
  have prev := renamePair append oldJoined oldL oldR oldAppend ρ stay
  have first := renamePair append mid (sa.relabel j) (oldR.relabel j) appMid k held
  have pWhole := renameCmp su oldJoined whole ρ stay
  have pLeft := renameCmp oldL sa left ρ stay
  have pRight := renameCmp oldR sb right ρ stay
  let S := su.relabel ρ
  let A := sa.relabel ρ
  let D := sb.relabel ρ
  let X := oldL.relabel ρ
  let Y := oldR.relabel ρ
  let W := oldJoined.relabel ρ
  let M := mid.relabel k
  have pM : Nonempty (Derivation B Ω (App A Y M)) := by
    simpa only [A,Y,M,ρ,← Term.relabel_relabel] using first
  have pJ : Nonempty (Derivation B Ω (App A D newJoined)) := by
    simpa only [A,D,ρ,← Term.relabel_relabel] using appNew
  have con1 := exact_LiteralCommonSuffixCongruence X A Y W M prev pM pLeft
  have con2 := exact_LiteralCommonPrefixCongruence A Y D M newJoined pM pJ pRight
  have obs := exact_LiteralObserverTransitivity S W newJoined pWhole
    (exact_LiteralObserverTransitivity W M newJoined con1 con2)
  have ss := renameParser u su parsed.source ρ Ω stay
  have aa := renameParser a sa parsed.kept ρ Ω stay
  have bb := renameParser b sb parsed.removed ρ Ω stay
  simpa only [ρ,← Term.relabel_relabel] using
    unionReportOfGraphs permutation (a.relabel ρ) (b.relabel ρ) (u.relabel ρ) A D S newJoined
      ⟨ss,aa,bb⟩ pJ obs

#print axioms exact_OriginalRawUnionFromEquivalentParts
end LogicLineages.PersistentMarking.NumberedWindowInternalRawUnionFromEquivalentPartsProof
