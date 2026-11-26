module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountZeroTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountZeroSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountZeroStepProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountSupportedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountZero
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRawListRecursion (recGraph)
open ID1Completion.InternalRawListRecursionProof (nilRecover consForward stepCases)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalControlGraphSupportProof (valueUnique outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalListInduction (atCode atIndex constructorBody constructors premises)
open ID1Completion.InternalListInductionProof (actualOriginalListInductionAtCode)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction)
open ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransport (constant)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseScratchMembership (memberBase memberStep)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename)
open NumberedWindowInternalSparseFilterInclusionSyntaxProof (missGraph)
open NumberedWindowInternalSparseFilterInclusionMemberConsProof (consInversion)
open NumberedWindowInternalSparseRetainedScanEqualityProof (equalityOfHit)
open NumberedWindowInternalLiteralCount (entryCount entryStep)
open NumberedWindowInternalLiteralCountSupportedTargets (counted)
open NumberedWindowInternalLiteralCountZeroTargets
open NumberedWindowInternalLiteralCountZeroSyntaxProof
open NumberedWindowInternalLiteralCountZeroStepProof (zeroStep)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem tapeTwo (c n : OTerm α) :
    (![c,n] : Fin 2 → OTerm α) = Fin.cons c (![n] : Fin 1 → OTerm α) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)) i

private theorem tapeThree (c h n : OTerm α) :
    (![c,h,n] : Fin 3 → OTerm α) = Fin.cons c (Fin.cons h (![n] : Fin 1 → OTerm α)) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q))) i

private theorem nilLaw (needle : OTerm α) :
    Nonempty (Derivation B Γ (zeroAt z needle)) := by
  let C := counted z needle z
  let H := memberGraph z needle
  have impossible := nilRecover memberBase memberStep (suc z) ![needle]
    (show Nonempty (Derivation B (H :: C :: Γ) H) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨bad⟩ := valueUnique memberBase (suc z) z ![needle] impossible (constantZeroValue ![needle])
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction (sucNeZeroApply bad))⟩

private theorem contradictionAtCons (code head tail needle previous : OTerm α)
    (cell : Nonempty (Derivation B Γ (consGraph code head tail)))
    (hit : Nonempty (Derivation B Γ (memberGraph code needle)))
    (prior : Nonempty (Derivation B Γ (counted tail needle previous)))
    (row : Nonempty (Derivation B Γ (programGraph entryStep z ![head,previous,needle])))
    (old : Nonempty (Derivation B Γ (zeroAt tail needle))) :
    Nonempty (Derivation B Γ (⊥ : Formula α)) := by
  obtain ⟨d⟩ := zeroStep head previous needle row
  obtain ⟨choice⟩ := consInversion code head tail needle cell hit
  obtain ⟨atZero⟩ := outputTransport entryCount previous z ![tail,needle]
    ⟨Derivation.conjunctionRight d⟩ prior
  obtain ⟨i⟩ := old
  let H := (missGraph head needle).not
  let T := memberGraph tail needle
  have first : Nonempty (Derivation B Γ (H.imp (⊥ : Formula α))) := by
    obtain ⟨same⟩ := equalityOfHit head needle (body := B) (Γ := H :: Γ)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction
      (Derivation.implicationElimination (addHyp (Derivation.conjunctionLeft d) H) same)⟩
  have tailNo := Derivation.implicationElimination i atZero
  obtain ⟨f⟩ := first
  exact ⟨disjunctionElimination choice f (Derivation.implicationIntroduction
    (Derivation.implicationElimination (addHyp tailNo T) (Derivation.hypothesis List.mem_cons_self)))⟩

private theorem consApply (code head tail needle : OTerm α)
    (cell : Nonempty (Derivation B Γ (consGraph code head tail)))
    (hit : Nonempty (Derivation B Γ (memberGraph code needle)))
    (run : Nonempty (Derivation B Γ (counted code needle z)))
    (old : Nonempty (Derivation B Γ (zeroAt tail needle))) :
    Nonempty (Derivation B Γ (⊥ : Formula α)) := by
  have actual : Nonempty (Derivation B Γ (recGraph (constant 1 0) entryStep z code ![needle])) := by
    simpa only [counted,tapeTwo,recGraph,entryCount] using run
  have opened := consForward (constant 1 0) entryStep code head tail z ![needle] cell actual
  apply stepCases (constant 1 0) entryStep z head tail ![needle] (⊥ : Formula α) opened
  intro β j Δ previous keep prior row
  have c := renameInto cell j Δ keep
  rw [consGraphRename] at c
  have h := renameInto hit j Δ keep
  rw [graphRename] at h
  have o := renameInto old j Δ keep
  rw [zeroRename] at o
  change Nonempty (Derivation B Δ (⊥ : Formula β))
  apply contradictionAtCons (code.relabel j) (head.relabel j) (tail.relabel j) (needle.relabel j)
    previous c h _ _ o
  · simpa only [counted,tapeTwo,recGraph,entryCount,inputsRename] using prior
  · simpa only [tapeThree,inputsRename,zRelabel] using row

private theorem consLaw (code head tail needle : OTerm α)
    (cell : Nonempty (Derivation B Γ (consGraph code head tail)))
    (old : Nonempty (Derivation B Γ (zeroAt tail needle))) :
    Nonempty (Derivation B Γ (zeroAt code needle)) := by
  let C := counted code needle z
  let H := memberGraph code needle
  obtain ⟨c⟩ := cell
  obtain ⟨o⟩ := old
  obtain ⟨bad⟩ := consApply (Γ := H :: C :: Γ) code head tail needle ⟨addHyp (addHyp c C) H⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨addHyp (addHyp o C) H⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction bad)⟩

private theorem constructorLaw (needle : OTerm α) :
    Nonempty (Derivation B Γ (constructors (zeroMotive needle))) := by
  apply actualFiniteUniversalIntroduction B α 3 Γ (constructorBody (zeroMotive needle))
  let j : α → α ⊕ Fin 3 := Sum.inl
  let c : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let h : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let t : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let C := consGraph c h t
  let I := zeroAt t (needle.relabel j)
  let Δ := I :: C :: Γ.map (fun f => f.relabel j)
  change Nonempty (Derivation B (Γ.map (fun f => f.relabel j))
    (C.imp ((atIndex (zeroMotive needle) 2).imp (atIndex (zeroMotive needle) 0))))
  simp only [zeroIndex]
  obtain ⟨d⟩ := consLaw (B := B) (Γ := Δ) c h t (needle.relabel j)
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction d)⟩

theorem exactLiteralZeroCount : ExactLiteralZeroCount := by
  intro B α Γ code needle
  have base : Nonempty (Derivation B Γ (atCode (zeroMotive needle) z)) := by
    rw [zeroCode]
    exact nilLaw needle
  obtain ⟨d⟩ := base
  obtain ⟨s⟩ := constructorLaw (B := B) (Γ := Γ) needle
  have h : Nonempty (Derivation B Γ (premises (zeroMotive needle))) :=
    ⟨Derivation.conjunctionIntroduction d s⟩
  have law := actualOriginalListInductionAtCode B α Γ (zeroMotive needle) code h
  rw [zeroCode] at law
  exact law

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountZero
