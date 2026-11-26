module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAllQueriesTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAbsentChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountSupportedChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountSupportedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOpenChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAllQueries
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (projectionValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (trans symm)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalScratchAppendOpenChecks (fromLeft fromRight)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)
open NumberedWindowInternalLiteralCount
open NumberedWindowInternalLiteralCountSupportedTargets (accepted counted)
open NumberedWindowInternalLiteralCountSupportedSyntaxProof (acceptedRename)
open NumberedWindowInternalLiteralCountSupportedChecks (exact_OpenLiteralSupportedCount)
open NumberedWindowInternalLiteralCountAbsentChecks (exact_OpenLiteralAbsentCountZero)
open NumberedWindowInternalLiteralCountAllQueriesTargets

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem noLeft (left right joined key : OTerm α)
    (appendReport : Nonempty (Derivation B Γ (programGraph append joined ![left,right])))
    (no : Nonempty (Derivation B Γ (memberGraph joined key).not)) :
    Nonempty (Derivation B Γ (memberGraph left key).not) := by
  let H := memberGraph left key
  obtain ⟨d⟩ := no
  obtain ⟨p⟩ := fromLeft left right joined key (withHyp appendReport H)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination (addHyp d H) p)⟩

private theorem noRight (left right joined key : OTerm α)
    (appendReport : Nonempty (Derivation B Γ (programGraph append joined ![left,right])))
    (no : Nonempty (Derivation B Γ (memberGraph joined key).not)) :
    Nonempty (Derivation B Γ (memberGraph right key).not) := by
  let H := memberGraph right key
  obtain ⟨d⟩ := no
  obtain ⟨p⟩ := fromRight left right joined key (withHyp appendReport H)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination (addHyp d H) p)⟩

theorem eachAtAppend (left right joined needle lc rc : OTerm α)
    (a : Nonempty (Derivation B Γ (programGraph append joined ![left,right])))
    (b : Nonempty (Derivation B Γ (accepted joined left right)))
    (l : Nonempty (Derivation B Γ (counted left needle lc)))
    (r : Nonempty (Derivation B Γ (counted right needle rc))) :
    Nonempty (Derivation B Γ (eqn lc rc)) := by
  let H := memberGraph joined needle
  apply formulaCases H
  · obtain ⟨all⟩ := exact_OpenLiteralSupportedCount B α (H :: Γ) joined left right needle lc rc
    obtain ⟨run⟩ := withHyp b H
    obtain ⟨los⟩ := withHyp l H
    obtain ⟨ros⟩ := withHyp r H
    have mem : Derivation B (H :: Γ) H := Derivation.hypothesis List.mem_cons_self
    exact ⟨Derivation.implicationElimination all (Derivation.conjunctionIntroduction run
      (Derivation.conjunctionIntroduction mem (Derivation.conjunctionIntroduction los ros)))⟩
  · have no : Nonempty (Derivation B (H.not :: Γ) H.not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨zl⟩ := exact_OpenLiteralAbsentCountZero B α (H.not :: Γ) left needle lc
    obtain ⟨zr⟩ := exact_OpenLiteralAbsentCountZero B α (H.not :: Γ) right needle rc
    obtain ⟨nl⟩ := noLeft left right joined needle (withHyp a H.not) no
    obtain ⟨nr⟩ := noRight left right joined needle (withHyp a H.not) no
    obtain ⟨los⟩ := withHyp l H.not
    obtain ⟨ros⟩ := withHyp r H.not
    exact ⟨trans
      (Derivation.implicationElimination zl (Derivation.conjunctionIntroduction nl los))
      (symm (Derivation.implicationElimination zr (Derivation.conjunctionIntroduction nr ros)))⟩

private theorem recoverFold (left right joined : OTerm α)
    (p : Nonempty (Derivation B Γ (programGraph permutation (suc z) ![left,right])))
    (a : Nonempty (Derivation B Γ (programGraph append joined ![left,right]))) :
    Nonempty (Derivation B Γ (accepted joined left right)) := by
  apply compositionRecover allCounts ![append,.projection 0,.projection 1] (suc z)
    ![left,right] ![joined,left,right] p
  intro i
  exact Fin.cases a (Fin.cases (projectionValue 0 ![left,right])
    (Fin.cases (projectionValue 1 ![left,right]) (fun x => Fin.elim0 x))) i

theorem eachAtPermutation (left right needle lc rc : OTerm α)
    (p : Nonempty (Derivation B Γ (programGraph permutation (suc z) ![left,right])))
    (l : Nonempty (Derivation B Γ (counted left needle lc)))
    (r : Nonempty (Derivation B Γ (counted right needle rc))) :
    Nonempty (Derivation B Γ (eqn lc rc)) := by
  apply programCases append ![left,right] (eqn lc rc)
  intro β j Δ joined keep appended
  rw [binaryInputsRename] at appended
  have q : Nonempty (Derivation B Δ (programGraph permutation (suc z)
      ![left.relabel j,right.relabel j])) := by
    simpa only [sucRelabel,zRelabel] using renamePair permutation (suc z) left right p j keep
  have x := renamePair entryCount lc left needle l j keep
  have y := renamePair entryCount rc right needle r j keep
  rw [eqnRelabel]
  exact eachAtAppend (left.relabel j) (right.relabel j) joined (needle.relabel j) (lc.relabel j) (rc.relabel j)
    appended (recoverFold (left.relabel j) (right.relabel j) joined q appended) x y

theorem exactOpenLiteralCountAgreement : ExactOpenLiteralCountAgreement := by
  intro B α Γ left right held
  unfold agreement
  apply actualFiniteUniversalIntroduction B α 3 Γ (agreementBody left right)
  let j : α → α ⊕ Fin 3 := Sum.inl
  let L := left.relabel j
  let R := right.relabel j
  let N : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let X : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let Y : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let H := counted L N X ⊓ counted R N Y
  let Δ := H :: Γ.map (fun q => q.relabel j)
  have keep : ∀ f ∈ Γ, f.relabel j ∈ Δ := by
    intro f hf
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
  have p : Nonempty (Derivation B Δ (programGraph permutation (suc z) ![L,R])) := by
    simpa only [L,R,sucRelabel,zRelabel] using renamePair permutation (suc z) left right held j keep
  have own : Derivation B Δ H := Derivation.hypothesis List.mem_cons_self
  obtain ⟨paid⟩ := eachAtPermutation L R N X Y p
    ⟨Derivation.conjunctionLeft own⟩ ⟨Derivation.conjunctionRight own⟩
  exact ⟨Derivation.implicationIntroduction paid⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAllQueries
