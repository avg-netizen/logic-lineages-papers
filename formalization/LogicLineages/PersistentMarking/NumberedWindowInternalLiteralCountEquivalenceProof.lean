module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAllQueriesTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalRawConsUnionReportThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAgreementBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountConverseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAllQueriesChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountReflexiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountMembershipChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountSupportedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountEquivalenceProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm trans)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)
open NumberedWindowInternalLiteralCount (permutation entryCount)
open NumberedWindowInternalLiteralCountSupportedTargets (counted)
open NumberedWindowInternalLiteralCountSupportedSyntaxProof (countedRename)
open NumberedWindowInternalLiteralCountAllQueriesTargets (agreement agreementBody)
open NumberedWindowInternalLiteralCountAllQueriesChecks (exact_OpenLiteralCountAgreement)
open NumberedWindowInternalLiteralCountAgreementBindingProof (agreementApply agreementRename)
open NumberedWindowInternalLiteralCountConverseProof (exact_LiteralAgreementAccept)
open NumberedWindowInternalLiteralCountReflexiveProof (exact_LiteralObserverReflexivity)
open NumberedWindowInternalLiteralCountMembershipChecks (exact_OpenLiteralCountMembershipForward)
open NumberedWindowInternalOriginalRawConsUnionReportThinProof (OpenObserverReflexivity)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem agreementSymm (left right : OTerm α)
    (shared : Nonempty (Derivation B Γ (agreement left right))) :
    Nonempty (Derivation B Γ (agreement right left)) := by
  unfold agreement
  apply actualFiniteUniversalIntroduction B α 3 Γ (agreementBody right left)
  let j : α → α ⊕ Fin 3 := Sum.inl
  let L := left.relabel j
  let R := right.relabel j
  let key : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let a : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let b : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let H := counted R key a ⊓ counted L key b
  let Δ := H :: Γ.map (fun q => q.relabel j)
  have keep : ∀ f ∈ Γ, f.relabel j ∈ Δ := by
    intro f hf
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
  have n := renameInto shared j Δ keep
  rw [agreementRename] at n
  have own : Derivation B Δ H := Derivation.hypothesis List.mem_cons_self
  obtain ⟨eq⟩ := agreementApply L R key b a n
    ⟨Derivation.conjunctionRight own⟩ ⟨Derivation.conjunctionLeft own⟩
  exact ⟨Derivation.implicationIntroduction (symm eq)⟩

private theorem transQuery (left middle right key lc rc : OTerm α)
    (a : Nonempty (Derivation B Γ (agreement left middle)))
    (b : Nonempty (Derivation B Γ (agreement middle right)))
    (leftCount : Nonempty (Derivation B Γ (counted left key lc)))
    (rightCount : Nonempty (Derivation B Γ (counted right key rc))) :
    Nonempty (Derivation B Γ (eqn lc rc)) := by
  apply programCases entryCount ![middle,key] (eqn lc rc)
  intro β j Δ mc keep hm
  rw [binaryInputsRename] at hm
  have ap := renameInto a j Δ keep
  have bp := renameInto b j Δ keep
  rw [agreementRename] at ap bp
  have lp := renameInto leftCount j Δ keep
  have rp := renameInto rightCount j Δ keep
  rw [countedRename] at lp rp
  obtain ⟨e⟩ := agreementApply (left.relabel j) (middle.relabel j) (key.relabel j)
    (lc.relabel j) mc ap lp hm
  obtain ⟨f⟩ := agreementApply (middle.relabel j) (right.relabel j) (key.relabel j)
    mc (rc.relabel j) bp hm rp
  rw [eqnRelabel]
  exact ⟨trans e f⟩

theorem agreementTrans (left middle right : OTerm α)
    (a : Nonempty (Derivation B Γ (agreement left middle)))
    (b : Nonempty (Derivation B Γ (agreement middle right))) :
    Nonempty (Derivation B Γ (agreement left right)) := by
  unfold agreement
  apply actualFiniteUniversalIntroduction B α 3 Γ (agreementBody left right)
  let j : α → α ⊕ Fin 3 := Sum.inl
  let L := left.relabel j
  let M := middle.relabel j
  let R := right.relabel j
  let key : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let x : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let y : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let H := counted L key x ⊓ counted R key y
  let Δ := H :: Γ.map (fun q => q.relabel j)
  have keep : ∀ f ∈ Γ, f.relabel j ∈ Δ := by
    intro f hf
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
  have ap := renameInto a j Δ keep
  have bp := renameInto b j Δ keep
  rw [agreementRename] at ap bp
  have own : Derivation B Δ H := Derivation.hypothesis List.mem_cons_self
  obtain ⟨q⟩ := transQuery L M R key x y ap bp
    ⟨Derivation.conjunctionLeft own⟩ ⟨Derivation.conjunctionRight own⟩
  exact ⟨Derivation.implicationIntroduction q⟩

theorem exact_LiteralEquivalenceReflexive (B : Positive (Fin 1)) :
    OpenObserverReflexivity B permutation :=
  exact_LiteralObserverReflexivity B

theorem exact_LiteralObserverSymmetry (left right : OTerm α)
    (h : Nonempty (Derivation B Γ (programGraph permutation (suc z) ![left,right]))) :
    Nonempty (Derivation B Γ (programGraph permutation (suc z) ![right,left])) :=
  exact_LiteralAgreementAccept B α Γ right left
    (agreementSymm left right (exact_OpenLiteralCountAgreement B α Γ left right h))

theorem exact_LiteralObserverTransitivity (left middle right : OTerm α)
    (a : Nonempty (Derivation B Γ (programGraph permutation (suc z) ![left,middle])))
    (b : Nonempty (Derivation B Γ (programGraph permutation (suc z) ![middle,right]))) :
    Nonempty (Derivation B Γ (programGraph permutation (suc z) ![left,right])) :=
  exact_LiteralAgreementAccept B α Γ left right
    (agreementTrans left middle right (exact_OpenLiteralCountAgreement B α Γ left middle a)
      (exact_OpenLiteralCountAgreement B α Γ middle right b))

theorem exact_LiteralMemberReverse (B : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (left right key : OTerm α)
    (h : Nonempty (Derivation B Γ (programGraph permutation (suc z) ![left,right])))
    (m : Nonempty (Derivation B Γ (memberGraph right key))) :
    Nonempty (Derivation B Γ (memberGraph left key)) :=
  exact_OpenLiteralCountMembershipForward B α Γ right left key (exact_LiteralObserverSymmetry left right h) m

#print axioms exact_LiteralEquivalenceReflexive
#print axioms exact_LiteralObserverSymmetry
#print axioms exact_LiteralObserverTransitivity
#print axioms exact_LiteralMemberReverse
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountEquivalenceProof
