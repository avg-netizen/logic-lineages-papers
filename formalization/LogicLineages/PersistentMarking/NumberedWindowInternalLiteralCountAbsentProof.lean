module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAbsentTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAbsentSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAbsentConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAbsent
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRawListRecursion (recGraph)
open ID1Completion.InternalRawListRecursionProof (nilRecover consForward stepCases)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel zRelabel)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalListInduction (atCode atIndex constructorBody constructors premises)
open ID1Completion.InternalListInductionProof (actualOriginalListInductionAtCode)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction)
open ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransport (constant)
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename)
open NumberedWindowInternalLiteralCount (entryCount entryStep)
open NumberedWindowInternalLiteralCountSupportedTargets (counted)
open NumberedWindowInternalLiteralCountAbsentTargets
open NumberedWindowInternalLiteralCountAbsentSyntaxProof
open NumberedWindowInternalLiteralCountAbsentConsProof (consAbsent)

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

private theorem nilLaw (needle out : OTerm α) :
    Nonempty (Derivation B Γ (absentAt z needle out)) := by
  let H := (memberGraph z needle).not ⊓ counted z needle out
  have h : Derivation B (H :: Γ) H := Derivation.hypothesis List.mem_cons_self
  have atNil : Nonempty (Derivation B (H :: Γ) (recGraph (constant 1 0) entryStep out z ![needle])) := by
    simpa only [counted,tapeTwo,recGraph,entryCount] using
      (show Nonempty (Derivation B (H :: Γ) (counted z needle out)) from ⟨Derivation.conjunctionRight h⟩)
  have q := nilRecover (constant 1 0) entryStep out ![needle] atNil
  obtain ⟨e⟩ := valueUnique (constant 1 0) out z ![needle] q (constantZeroValue ![needle])
  exact ⟨Derivation.implicationIntroduction e⟩

private theorem consApply (code head tail needle out : OTerm α)
    (cell : Nonempty (Derivation B Γ (consGraph code head tail)))
    (no : Nonempty (Derivation B Γ (memberGraph code needle).not))
    (run : Nonempty (Derivation B Γ (counted code needle out)))
    (old : Nonempty (Derivation B Γ (absentAt tail needle out))) :
    Nonempty (Derivation B Γ (eqn out z)) := by
  have actual : Nonempty (Derivation B Γ (recGraph (constant 1 0) entryStep out code ![needle])) := by
    simpa only [counted,tapeTwo,recGraph,entryCount] using run
  have opened := consForward (constant 1 0) entryStep code head tail out ![needle] cell actual
  apply stepCases (constant 1 0) entryStep out head tail ![needle] (eqn out z) opened
  intro β j Δ previous keep prior row
  have c := renameInto cell j Δ keep
  rw [consGraphRename] at c
  have n := renameInto no j Δ keep
  change Nonempty (Derivation B Δ ((memberGraph code needle).relabel j).not) at n
  rw [graphRename] at n
  have o := renameInto old j Δ keep
  rw [absentRename] at o
  rw [eqnRelabel,zRelabel]
  apply consAbsent (code.relabel j) (head.relabel j) (tail.relabel j) (needle.relabel j)
    previous (out.relabel j) c n _ _ o
  · simpa only [counted,tapeTwo,recGraph,entryCount,inputsRename] using prior
  · simpa only [tapeThree,inputsRename] using row

private theorem consLaw (code head tail needle out : OTerm α)
    (cell : Nonempty (Derivation B Γ (consGraph code head tail)))
    (old : Nonempty (Derivation B Γ (absentAt tail needle out))) :
    Nonempty (Derivation B Γ (absentAt code needle out)) := by
  let H := (memberGraph code needle).not ⊓ counted code needle out
  have h : Derivation B (H :: Γ) H := Derivation.hypothesis List.mem_cons_self
  obtain ⟨c⟩ := cell
  obtain ⟨o⟩ := old
  obtain ⟨v⟩ := consApply code head tail needle out ⟨addHyp c H⟩
    ⟨Derivation.conjunctionLeft h⟩ ⟨Derivation.conjunctionRight h⟩ ⟨addHyp o H⟩
  exact ⟨Derivation.implicationIntroduction v⟩

private theorem constructorLaw (needle out : OTerm α) :
    Nonempty (Derivation B Γ (constructors (absentMotive needle out))) := by
  apply actualFiniteUniversalIntroduction B α 3 Γ (constructorBody (absentMotive needle out))
  let j : α → α ⊕ Fin 3 := Sum.inl
  let c : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let h : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let t : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let C := consGraph c h t
  let I := absentAt t (needle.relabel j) (out.relabel j)
  let Δ := I :: C :: Γ.map (fun f => f.relabel j)
  change Nonempty (Derivation B (Γ.map (fun f => f.relabel j))
    (C.imp ((atIndex (absentMotive needle out) 2).imp (atIndex (absentMotive needle out) 0))))
  simp only [absentIndex]
  obtain ⟨d⟩ := consLaw (B := B) (Γ := Δ) c h t (needle.relabel j) (out.relabel j)
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction d)⟩

theorem exactLiteralAbsentCount : ExactLiteralAbsentCount := by
  intro B α Γ code needle out
  have base : Nonempty (Derivation B Γ (atCode (absentMotive needle out) z)) := by
    rw [absentCode]
    exact nilLaw needle out
  obtain ⟨d⟩ := base
  obtain ⟨s⟩ := constructorLaw (B := B) (Γ := Γ) needle out
  have h : Nonempty (Derivation B Γ (premises (absentMotive needle out))) :=
    ⟨Derivation.conjunctionIntroduction d s⟩
  have law := actualOriginalListInductionAtCode B α Γ (absentMotive needle out) code h
  rw [absentCode] at law
  exact law

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAbsent
