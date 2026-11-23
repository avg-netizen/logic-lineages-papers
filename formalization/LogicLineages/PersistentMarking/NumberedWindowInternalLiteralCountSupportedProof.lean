module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountSupportedTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountSupportedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountSupportedConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountSupported
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRawListRecursion (recGraph)
open ID1Completion.InternalRawListRecursionProof (nilRecover consForward stepCases)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalListInduction (atCode atIndex constructorBody constructors premises)
open ID1Completion.InternalListInductionProof (actualOriginalListInductionAtCode)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction)
open ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransport (constant)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseScratchMembership (memberBase memberStep)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalLiteralCount
open NumberedWindowInternalLiteralCountSupportedTargets
open NumberedWindowInternalLiteralCountSupportedSyntaxProof
open NumberedWindowInternalLiteralCountSupportedConsProof (consCompare)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem nilFalse (needle : OTerm α)
    (h : Nonempty (Derivation B Γ (memberGraph z needle))) :
    Nonempty (Derivation B Γ (⊥ : Formula α)) := by
  have bad := nilRecover memberBase memberStep (suc z) ![needle] h
  obtain ⟨e⟩ := valueUnique memberBase (suc z) z ![needle] bad (constantZeroValue ![needle])
  exact ⟨sucNeZeroApply e⟩

private theorem nilQuery (left right needle lc rc : OTerm α) :
    Nonempty (Derivation B Γ (query z left right needle lc rc)) := by
  let H := prem z left right needle lc rc
  have own : Derivation B (H :: Γ) H := Derivation.hypothesis List.mem_cons_self
  have rest := Derivation.conjunctionRight own
  obtain ⟨bad⟩ := nilFalse needle ⟨Derivation.conjunctionLeft rest⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.explosion bad)⟩

private theorem tapeThree (c l r : OTerm α) :
    (![c,l,r] : Fin 3 → OTerm α) = Fin.cons c (![l,r] : Fin 2 → OTerm α) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q))) i

private theorem tapeFour (c a l r : OTerm α) :
    (![c,a,l,r] : Fin 4 → OTerm α) = Fin.cons c (Fin.cons a (![l,r] : Fin 2 → OTerm α)) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)))) i

private theorem consApply (code head tail left right needle lc rc : OTerm α)
    (cell : Nonempty (Derivation B Γ (consGraph code head tail)))
    (ih : Nonempty (Derivation B Γ (query tail left right needle lc rc)))
    (run : Nonempty (Derivation B Γ (accepted code left right)))
    (member : Nonempty (Derivation B Γ (memberGraph code needle)))
    (l : Nonempty (Derivation B Γ (counted left needle lc)))
    (r : Nonempty (Derivation B Γ (counted right needle rc))) :
    Nonempty (Derivation B Γ (eqn lc rc)) := by
  have h : Nonempty (Derivation B Γ (recGraph (constant 2 1) step (suc z) code ![left,right])) := by
    simpa only [accepted,tapeThree,recGraph,allCounts] using run
  have opened := consForward (constant 2 1) step code head tail (suc z) ![left,right] cell h
  apply stepCases (constant 2 1) step (suc z) head tail ![left,right] (eqn lc rc) opened
  intro β j Δ acc keep prior row
  have c' := renameInto cell j Δ keep
  have i' := renameInto ih j Δ keep
  have m' := renameInto member j Δ keep
  have l' := renameInto l j Δ keep
  have r' := renameInto r j Δ keep
  rw [consGraphRename] at c'
  rw [queryRename] at i'
  rw [graphRename] at m'
  rw [countedRename] at l' r'
  rw [eqnRelabel]
  apply consCompare (code.relabel j) (head.relabel j) (tail.relabel j) acc
    (left.relabel j) (right.relabel j) (needle.relabel j) (lc.relabel j) (rc.relabel j) c' _ _ m' l' r' i'
  · simpa only [recGraph,allCounts,tapeThree,binaryInputsRename] using prior
  · simpa only [tapeFour,binaryInputsRename,sucRelabel,zRelabel] using row

private theorem consQuery (code head tail left right needle lc rc : OTerm α)
    (cell : Nonempty (Derivation B Γ (consGraph code head tail)))
    (ih : Nonempty (Derivation B Γ (query tail left right needle lc rc))) :
    Nonempty (Derivation B Γ (query code left right needle lc rc)) := by
  let H := prem code left right needle lc rc
  have own : Derivation B (H :: Γ) H := Derivation.hypothesis List.mem_cons_self
  have rest := Derivation.conjunctionRight own
  have cs := Derivation.conjunctionRight rest
  obtain ⟨c⟩ := cell
  obtain ⟨i⟩ := ih
  obtain ⟨out⟩ := consApply code head tail left right needle lc rc ⟨addHyp c H⟩ ⟨addHyp i H⟩
    ⟨Derivation.conjunctionLeft own⟩ ⟨Derivation.conjunctionLeft rest⟩
    ⟨Derivation.conjunctionLeft cs⟩ ⟨Derivation.conjunctionRight cs⟩
  exact ⟨Derivation.implicationIntroduction out⟩

private theorem constructorLaw (left right needle lc rc : OTerm α) :
    Nonempty (Derivation B Γ (constructors (motive left right needle lc rc))) := by
  apply actualFiniteUniversalIntroduction B α 3 Γ (constructorBody (motive left right needle lc rc))
  let j : α → α ⊕ Fin 3 := Sum.inl
  let c : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let h : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let t : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let C := consGraph c h t
  let p := motive left right needle lc rc
  let I := query t (left.relabel j) (right.relabel j) (needle.relabel j) (lc.relabel j) (rc.relabel j)
  let Δ := I :: C :: Γ.map (fun f => f.relabel j)
  change Nonempty (Derivation B (Γ.map (fun f => f.relabel j))
    (C.imp ((atIndex p 2).imp (atIndex p 0))))
  simp only [p,motiveIndex]
  obtain ⟨d⟩ := consQuery (B := B) (Γ := Δ) c h t
    (left.relabel j) (right.relabel j) (needle.relabel j) (lc.relabel j) (rc.relabel j)
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction d)⟩

theorem exactOpenSupportedCount : ExactOpenSupportedCount := by
  intro B α Γ code left right needle lc rc
  have base : Nonempty (Derivation B Γ (atCode (motive left right needle lc rc) z)) := by
    rw [motiveCode]
    exact nilQuery left right needle lc rc
  obtain ⟨d⟩ := base
  obtain ⟨s⟩ := constructorLaw (B := B) (Γ := Γ) left right needle lc rc
  have h : Nonempty (Derivation B Γ (premises (motive left right needle lc rc))) :=
    ⟨Derivation.conjunctionIntroduction d s⟩
  have all := actualOriginalListInductionAtCode B α Γ (motive left right needle lc rc) code h
  rw [motiveCode] at all
  exact all

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountSupported
