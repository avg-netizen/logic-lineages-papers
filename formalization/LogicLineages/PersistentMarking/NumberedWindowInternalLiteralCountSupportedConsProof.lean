module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountSupportedTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountSupportedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountStepProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountSupportedConsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (equalEqn outputTransport programRename)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof
  (binaryInputsRename tripleInputsRename quadInputsRename)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseFilterInclusionSyntaxProof (missGraph)
open NumberedWindowInternalSparseFilterInclusionMemberConsProof (consInversion)
open NumberedWindowInternalSparseRetainedScanEqualityProof (equalityOfHit)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalLiteralCount
open NumberedWindowInternalLiteralCountStepProof (stepRecover)
open NumberedWindowInternalLiteralCountSupportedTargets
open NumberedWindowInternalLiteralCountSupportedSyntaxProof (acceptedRename)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem moveNeedle (list old key value : OTerm α)
    (e : Nonempty (Derivation B Γ (eqn old key)))
    (h : Nonempty (Derivation B Γ (counted list old value))) :
    Nonempty (Derivation B Γ (counted list key value)) := by
  unfold counted programGraph at h ⊢
  apply graphInputTransport B α 2 Γ (OrdinaryArithmetic.graphFormula entryCount)
    value ![list,old] ![list,key] _ h
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change Nonempty (Derivation B Γ (equal list list))
    rw [equalEqn]
    exact ⟨ID1Completion.InternalTagArithmeticSupportProof.refl list⟩
  · obtain rfl := Fin.eq_zero j
    change Nonempty (Derivation B Γ (equal old key))
    rw [equalEqn]
    exact e

private theorem renameStep {β : Type} {Δ : List (Formula β)} (head acc left right : OTerm α)
    (h : Nonempty (Derivation B Γ (programGraph step (suc z) ![head,acc,left,right])))
    (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    Nonempty (Derivation B Δ (programGraph step (suc z)
      ![head.relabel j,acc.relabel j,left.relabel j,right.relabel j])) := by
  simpa only [programRename,quadInputsRename,sucRelabel,zRelabel] using renameInto h j Δ keep

private theorem acceptedTail (head acc tail left right : OTerm α)
    (prior : Nonempty (Derivation B Γ (programGraph allCounts acc ![tail,left,right])))
    (row : Nonempty (Derivation B Γ (programGraph step (suc z) ![head,acc,left,right]))) :
    Nonempty (Derivation B Γ (accepted tail left right)) := by
  apply programCases entryCount ![left,head] (accepted tail left right)
  intro β j Δ lh keep hLeft
  rw [binaryInputsRename] at hLeft
  let h := head.relabel j
  let n := acc.relabel j
  let t := tail.relabel j
  let l := left.relabel j
  let r := right.relabel j
  have rd := renameStep head acc left right row j keep
  have ready : Nonempty (Derivation B Δ (programGraph allCounts n ![t,l,r])) := by
    simpa only [h,n,t,l,r,programRename,tripleInputsRename] using renameInto prior j Δ keep
  rw [acceptedRename]
  apply programCases entryCount ![r,h] (accepted t l r)
  intro γ k Ω rh retain hRight
  rw [binaryInputsRename] at hRight
  have keptLeft := renamePair entryCount lh l h hLeft k retain
  have both := stepRecover (h.relabel k) (n.relabel k) (l.relabel k) (r.relabel k) (lh.relabel k) rh
    keptLeft hRight (renameStep h n l r rd k retain)
  obtain ⟨ok⟩ := both
  have p : Nonempty (Derivation B Ω (programGraph allCounts (n.relabel k)
      ![t.relabel k,l.relabel k,r.relabel k])) := by
    simpa only [programRename,tripleInputsRename] using renameInto ready k Ω retain
  rw [acceptedRename]
  exact outputTransport allCounts (n.relabel k) (suc z) ![t.relabel k,l.relabel k,r.relabel k]
    ⟨Derivation.conjunctionRight ok⟩ p

theorem consCompare (code head tail acc left right needle lc rc : OTerm α)
    (cell : Nonempty (Derivation B Γ (consGraph code head tail)))
    (prior : Nonempty (Derivation B Γ (programGraph allCounts acc ![tail,left,right])))
    (row : Nonempty (Derivation B Γ (programGraph step (suc z) ![head,acc,left,right])))
    (member : Nonempty (Derivation B Γ (memberGraph code needle)))
    (l : Nonempty (Derivation B Γ (counted left needle lc)))
    (r : Nonempty (Derivation B Γ (counted right needle rc)))
    (ih : Nonempty (Derivation B Γ (query tail left right needle lc rc))) :
    Nonempty (Derivation B Γ (eqn lc rc)) := by
  obtain ⟨choice⟩ := consInversion code head tail needle cell member
  obtain ⟨l⟩ := l
  obtain ⟨r⟩ := r
  obtain ⟨a⟩ := row
  obtain ⟨i⟩ := ih
  let H := (missGraph head needle).not
  let T := memberGraph tail needle
  have first : Nonempty (Derivation B Γ (H.imp (eqn lc rc))) := by
    obtain ⟨e⟩ := equalityOfHit head needle (body := B) (Γ := H :: Γ)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have eq := ID1Completion.InternalTagArithmeticSupportProof.symm e
    have x := moveNeedle left needle head lc ⟨eq⟩ ⟨addHyp l H⟩
    have y := moveNeedle right needle head rc ⟨eq⟩ ⟨addHyp r H⟩
    obtain ⟨d⟩ := stepRecover head acc left right lc rc x y ⟨addHyp a H⟩
    exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionLeft d)⟩
  have second : Nonempty (Derivation B Γ (T.imp (eqn lc rc))) := by
    obtain ⟨trueTail⟩ := acceptedTail head acc tail left right prior ⟨a⟩
    have h : Derivation B (T :: Γ) T := Derivation.hypothesis List.mem_cons_self
    have premTail : Derivation B (T :: Γ) (prem tail left right needle lc rc) :=
      Derivation.conjunctionIntroduction (addHyp trueTail T)
        (Derivation.conjunctionIntroduction h
          (Derivation.conjunctionIntroduction (addHyp l T) (addHyp r T)))
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination (addHyp i T) premTail)⟩
  obtain ⟨h⟩ := first
  obtain ⟨t⟩ := second
  exact ⟨disjunctionElimination choice h t⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountSupportedConsProof
