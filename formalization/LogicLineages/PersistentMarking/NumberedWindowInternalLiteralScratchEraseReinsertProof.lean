module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseActualCountEffectProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountConverseProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseReinsertProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (trans symm addSucc addZero congSuc)
open InternalControlGraphSupportProof (valueUnique)
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open InternalAcceptanceSupportProof (programCases)
open InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalLiteralCount (entryCount permutation)
open NumberedWindowInternalLiteralCountSupportedTargets (counted)
open NumberedWindowInternalLiteralCountAllQueriesTargets (agreement agreementBody)
open NumberedWindowInternalLiteralCountConverseProof (exact_LiteralAgreementAccept)
open NumberedWindowInternalLiteralCountOpenConsProof (chosenHead otherHead)
open NumberedWindowInternalLiteralScratchErase (state)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalLiteralScratchEraseCountEffectProof (countEffect applyAt countEffectRename)
open NumberedWindowInternalLiteralScratchEraseReportSuppliersProof (bitReport)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

private theorem introAgreement (left right : OTerm alpha)
    (each : ∀ (β : Type) (j : alpha → β) (Γ : List (Formula β)) (key lc rc : OTerm β),
      (∀ f ∈ Delta, f.relabel j ∈ Γ) →
      Nonempty (Derivation body Γ (counted (left.relabel j) key lc)) →
      Nonempty (Derivation body Γ (counted (right.relabel j) key rc)) →
      Nonempty (Derivation body Γ (eqn lc rc))) :
    Nonempty (Derivation body Delta (agreement left right)) := by
  unfold agreement
  apply actualFiniteUniversalIntroduction body alpha 3 Delta (agreementBody left right)
  let j : alpha → alpha ⊕ Fin 3 := Sum.inl
  let key : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
  let lc : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
  let rc : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
  let H := counted (left.relabel j) key lc ⊓ counted (right.relabel j) key rc
  let Γ := H :: Delta.map (fun q => q.relabel j)
  have keep : ∀ f ∈ Delta, f.relabel j ∈ Γ := by
    intro f hf
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
  have own : Derivation body Γ H := Derivation.hypothesis List.mem_cons_self
  obtain ⟨e⟩ := each (alpha ⊕ Fin 3) j Γ key lc rc keep
    ⟨Derivation.conjunctionLeft own⟩ ⟨Derivation.conjunctionRight own⟩
  exact ⟨Derivation.implicationIntroduction e⟩

private theorem sameCounts (raw needle rest rebuilt key old new leftover : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rebuilt needle rest)))
    (rep : Nonempty (Derivation body Delta (countEffect raw needle rest (suc z))))
    (hl : Nonempty (Derivation body Delta (counted raw key old)))
    (hr : Nonempty (Derivation body Delta (counted rebuilt key new)))
    (ht : Nonempty (Derivation body Delta (counted rest key leftover))) :
    Nonempty (Derivation body Delta (eqn old new)) := by
  let E := eqn needle key
  have changeCount := applyAt raw needle rest (suc z) key old leftover rep hl ht
  apply formulaCases E
  · have hq : Nonempty (Derivation body (E :: Delta) E) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have c := chosenHead rebuilt needle rest key leftover (withHyp hc E) (withHyp ht E) hq
    obtain ⟨eNew⟩ := valueUnique entryCount new (suc leftover) ![rebuilt,key] (withHyp hr E) c
    obtain ⟨hrep⟩ := withHyp changeCount E
    obtain ⟨q⟩ := hq
    have plus := Derivation.implicationElimination (Derivation.conjunctionLeft hrep) q
    have one : Derivation body (E :: Delta)
        (eqn (OrdinaryArithmetic.addTerm leftover (suc z)) (suc leftover)) :=
      trans (addSucc leftover z) (congSuc (addZero leftover))
    exact ⟨trans (trans plus one) (symm eNew)⟩
  · have hq : Nonempty (Derivation body (E.not :: Delta) E.not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have c := otherHead rebuilt needle rest key leftover (withHyp hc E.not) (withHyp ht E.not) hq
    obtain ⟨eNew⟩ := valueUnique entryCount new leftover ![rebuilt,key] (withHyp hr E.not) c
    obtain ⟨hrep⟩ := withHyp changeCount E.not
    obtain ⟨q⟩ := hq
    exact ⟨trans (Derivation.implicationElimination (Derivation.conjunctionRight hrep) q) (symm eNew)⟩

private theorem eachCount (raw needle rest rebuilt key old new : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rebuilt needle rest)))
    (rep : Nonempty (Derivation body Delta (countEffect raw needle rest (suc z))))
    (hl : Nonempty (Derivation body Delta (counted raw key old)))
    (hr : Nonempty (Derivation body Delta (counted rebuilt key new))) :
    Nonempty (Derivation body Delta (eqn old new)) := by
  apply programCases entryCount ![rest,key] _
  intro beta j Γ value keep h
  rw [binaryInputsRename] at h
  rw [eqnRelabel]
  have hj := renameInto hc j Γ keep
  rw [graph2Rename] at hj
  have report := renameInto rep j Γ keep
  simp only [countEffectRename,sucRelabel,zRelabel] at report
  have lj := renameInto hl j Γ keep
  have rj := renameInto hr j Γ keep
  simp only [counted,InternalControlGraphSupportProof.programRename,binaryInputsRename] at lj rj
  exact sameCounts (raw.relabel j) (needle.relabel j) (rest.relabel j) (rebuilt.relabel j)
    (key.relabel j) (old.relabel j) (new.relabel j) value hj report lj rj h

/-- Successful deletion followed by one real cons of the same needle gives
the original literal comparator, proved by one internal all-needle report. -/
theorem reinsert (raw needle acc bit rest rebuilt : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 state acc raw needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc bit rest)))
    (hfound : Nonempty (Derivation body Delta (eqn bit (suc z))))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rebuilt needle rest))) :
    Nonempty (Derivation body Delta (programGraph permutation (suc z) ![raw,rebuilt])) := by
  have effect := NumberedWindowInternalLiteralScratchEraseActualCountEffectProof.actualResult raw needle acc bit rest hv hp
  have success := bitReport raw needle rest bit (suc z) hfound effect
  apply exact_LiteralAgreementAccept body alpha Delta raw rebuilt
  apply introAgreement raw rebuilt
  intro beta j Γ key lc rc keep hl hr
  have hj := renameInto hc j Γ keep
  rw [graph2Rename] at hj
  have report := renameInto success j Γ keep
  simp only [countEffectRename,sucRelabel,zRelabel] at report
  exact eachCount (raw.relabel j) (needle.relabel j) (rest.relabel j) (rebuilt.relabel j)
    key lc rc hj report hl hr

/-- Actual open membership supplies the one flag for this same exact run. -/
theorem reinsertOfMember (raw needle acc bit rest rebuilt : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 state acc raw needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc bit rest)))
    (hm : Nonempty (Derivation body Delta (memberGraph raw needle)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rebuilt needle rest))) :
    Nonempty (Derivation body Delta (programGraph permutation (suc z) ![raw,rebuilt])) :=
  reinsert raw needle acc bit rest rebuilt hv hp
    (NumberedWindowInternalLiteralScratchEraseFoundProof.found raw needle acc bit rest hv hp hm) hc

#print axioms reinsert
#print axioms reinsertOfMember
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseReinsertProof
