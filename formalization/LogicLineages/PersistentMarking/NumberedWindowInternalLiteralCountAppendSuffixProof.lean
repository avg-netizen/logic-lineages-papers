module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendAgreementProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendSwapProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountEquivalenceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendSuffixProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalLiteralCountAppendCoreProof (appended)
open NumberedWindowInternalLiteralCountAppendSwapProof (exact_LiteralAppendSwap)
open NumberedWindowInternalLiteralCountAppendAgreementProof (exact_LiteralCommonPrefixCongruence)
open NumberedWindowInternalLiteralCountEquivalenceProof (exact_LiteralObserverTransitivity)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Append the same actual suffix to both literal multiplicity operands.
The given ordered appends are retained; both swapped reports are supplied
by original append graph totality, not existential assumptions. -/
theorem exact_LiteralCommonSuffixCongruence (left right suffix ls rs : OTerm α)
    (l : Nonempty (Derivation B Γ (appended left suffix ls)))
    (r : Nonempty (Derivation B Γ (appended right suffix rs)))
    (h : Nonempty (Derivation B Γ (programGraph permutation (suc z) ![left,right]))) :
    Nonempty (Derivation B Γ (programGraph permutation (suc z) ![ls,rs])) := by
  apply programCases append ![suffix,left] _
  intro β j Δ sl keep slReport
  rw [binaryInputsRename] at slReport
  simp only [programRename,binaryInputsRename,sucRelabel,zRelabel]
  let S := suffix.relabel j
  let L := left.relabel j
  let R := right.relabel j
  let LS := ls.relabel j
  let RS := rs.relabel j
  have l₁ := renamePair append ls left suffix l j keep
  have r₁ := renamePair append rs right suffix r j keep
  have h₁ : Nonempty (Derivation B Δ (programGraph permutation (suc z) ![L,R])) := by
    simpa only [sucRelabel,zRelabel,L,R] using renamePair permutation (suc z) left right h j keep
  have leftSwap := exact_LiteralAppendSwap L S LS sl l₁ slReport
  apply programCases append ![S,R] (programGraph permutation (suc z) ![LS,RS])
  intro γ k Ω sr retain srReport
  rw [binaryInputsRename] at srReport
  simp only [programRename,binaryInputsRename,sucRelabel,zRelabel]
  let sr0 := sl.relabel k
  let L₂ := L.relabel k
  let R₂ := R.relabel k
  let S₂ := S.relabel k
  let LS₂ := LS.relabel k
  let RS₂ := RS.relabel k
  have left₂ : Nonempty (Derivation B Ω (programGraph permutation (suc z) ![LS₂,sr0])) := by
    simpa only [sucRelabel,zRelabel,LS₂,sr0] using renamePair permutation (suc z) LS sl leftSwap k retain
  have core₂ : Nonempty (Derivation B Ω (programGraph permutation (suc z) ![L₂,R₂])) := by
    simpa only [sucRelabel,zRelabel,L₂,R₂] using renamePair permutation (suc z) L R h₁ k retain
  have middle := exact_LiteralCommonPrefixCongruence S₂ L₂ R₂ sr0 sr
    (renamePair append sl S L slReport k retain) srReport core₂
  have endSwap := exact_LiteralAppendSwap S₂ R₂ sr RS₂ srReport
    (renamePair append RS R S r₁ k retain)
  exact exact_LiteralObserverTransitivity LS₂ sr RS₂
    (exact_LiteralObserverTransitivity LS₂ sr0 sr left₂ middle) endSwap

#print axioms exact_LiteralCommonSuffixCongruence
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendSuffixProof
