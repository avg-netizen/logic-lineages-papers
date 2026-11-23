module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSingletonBottomTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowAtomicPositiveChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSingletonBottom
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalControlGraphSupportProof (equalEqn)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelope (run applyUnary exactBody)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (applyValue bothAccept bodyArity)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
  (cellAt headTailOfCell splitUnpack packOfUnpack emptyUnpack)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (packedArity canonicalCell)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (makeUnary packedBody)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalAtomicRefinement (bottomSource)
open NumberedWindowInternalAtomicRefinementNumericChecks (exact_NumericAtomicRecognizers)
open NumberedWindowInternalAtomicRefinementObjectChecks (exact_OpenAtomicRecognition)
open NumberedWindowInternalAtomicRefinementObjectTargets (packedBottomTerm)
open NumberedWindowAtomicPositiveTargets (bottomAddress)
open NumberedWindowAtomicPositiveChecks (exact_ConcreteAtomicAddressPositive)
open NumberedWindowInternalSingletonBottomTargets
open NumberedWindowFieldAlgorithm (pack unpack)
open NumberedWindowDirectAlgorithm (directLists readWitness)

private theorem singletonUnpack (a : Nat) : unpack (pack [a]) = some [a] := by
  change unpack (NumberedWindowPairAlgorithm.pair a 0 + 1) = _
  rw [splitUnpack (cellAt a 0),emptyUnpack] <;> rfl

private theorem singletonHead (a : Nat) : run cellHead (pack [a]) = a :=
  (headTailOfCell (cellAt a 0)).1

theorem exactNumericSingletonBottom : ExactNumericSingletonBottom := by
  intro x
  unfold recognize
  rw [bothAccept,bodyArity,applyValue]
  constructor
  · rintro ⟨⟨l,parsed,len⟩,hit⟩
    obtain ⟨a,rfl⟩ : ∃ a, l = [a] := by
      cases l with
      | nil => simp at len
      | cons a as =>
        cases as with
        | nil => exact ⟨a,rfl⟩
        | cons h t => simp at len
    have code := packOfUnpack x parsed
    rw [code,singletonHead] at hit
    obtain ⟨ctx,t,ha⟩ := (exact_NumericAtomicRecognizers a).2.1.mp hit
    exact ⟨ctx,t,code.trans (congrArg (fun u => pack [u]) ha)⟩
  · rintro ⟨ctx,t,rfl⟩
    refine ⟨⟨_,singletonUnpack _,rfl⟩,?_⟩
    rw [singletonHead]
    exact (exact_NumericAtomicRecognizers (bottomAddress ctx t)).2.1.mpr ⟨ctx,t,rfl⟩

theorem exactOpenSingletonBottom : ExactOpenSingletonBottom := by
  intro B α Γ ctx t
  let h := packedBottomTerm ctx t
  let input := packedSingletonBottom ctx t
  obtain ⟨cell⟩ := canonicalCell (body := B) (Γ := Γ) h z
  have same : Nonempty (Derivation B Γ (equal h (packedBottomTerm ctx t))) := by
    change Nonempty (Derivation B Γ (equal h h))
    rw [equalEqn]
    exact ⟨ID1Completion.InternalTagArithmeticSupportProof.refl h⟩
  obtain ⟨atom⟩ := exact_OpenAtomicRecognition.2 B α Γ h ctx t same
  have shape : Nonempty (Derivation B Γ (programGraph (exactBody 1) (suc z) ![input])) :=
    packedArity (body := B) (Γ := Γ) [h]
  have atomHead : Nonempty (Derivation B Γ (programGraph (applyUnary bottomSource cellHead)
      (suc z) ![input])) :=
    makeUnary bottomSource cellHead (suc z) input h ⟨Derivation.conjunctionRight atom⟩
      ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight cell)⟩
  exact conjunctionAccept (exactBody 1) (applyUnary bottomSource cellHead) ![input] shape atomHead

private theorem singletonRemoval (a : Nat) (kept removed : List Nat)
    (h : [a].Perm (kept ++ removed)) (hn : removed ≠ []) :
    kept = [] ∧ removed = [a] := by
  cases removed with
  | nil => exact (hn rfl).elim
  | cons b tail =>
    have hl := h.length_eq
    have hk : kept.length = 0 := by simp at hl; omega
    have ht : tail.length = 0 := by simp at hl; omega
    have ke := List.eq_nil_of_length_eq_zero hk
    have te := List.eq_nil_of_length_eq_zero ht
    subst kept
    subst tail
    have hb : b ∈ [a] := h.mem_iff.mpr (by simp)
    simp at hb
    simp [hb]

private theorem onlyDeletion (scalar : Nat → Bool) (positive : Nat → Nat → Nat → Bool)
    (a : Nat) (ys : List Nat) (wit : NumberedWindowDirectAlgorithm.Witness)
    (terminal : ∀ w y, positive a w y = false) :
    directLists scalar positive [a] ys wit = true → ys = [] := by
  intro h
  simp only [directLists,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨_,_⟩,source⟩,target⟩,nonempty⟩,added⟩ := h
  have hn : wit.2.1 ≠ [] := by
    intro he
    simp [he] at nonempty
  obtain ⟨hk,hr⟩ := singletonRemoval a wit.1 wit.2.1 source hn
  have hi : wit.2.2 = [] := by
    cases h : wit.2.2 with
    | nil => rfl
    | cons e es =>
      have bad := (List.all_eq_true.mp added) e (by rw [h]; simp)
      simp only [Bool.and_eq_true] at bad
      have dom : e.2.1 = a := by simpa [hr] using bad.1
      have pos := bad.2
      rw [dom,terminal] at pos <;> contradiction
  apply List.eq_nil_of_length_eq_zero
  simpa [hk,hi] using target.length_eq

theorem exactDirectSingletonBottomTarget : ExactDirectSingletonBottomTarget := by
  intro xs s ctx t w y h
  unfold NumberedWindowConcreteCheckers.direct NumberedWindowAddressCheckers.direct
    NumberedWindowDirectAlgorithm.direct at h
  rw [singletonUnpack] at h
  cases hw : readWitness w with
  | none => simp [hw] at h
  | some wit =>
    cases hy : unpack y with
    | none => simp [hw,hy] at h
    | some ys =>
      have ht : directLists (NumberedWindowScalarAlgorithm.scalar s)
          (NumberedWindowConcreteCheckers.positive xs s) [bottomAddress ctx t] ys wit = true := by
        simpa only [hw,hy,NumberedWindowConcreteCheckers.positive] using h
      have out := onlyDeletion _ _ _ _ _ (exact_ConcreteAtomicAddressPositive.2 xs s ctx t) ht
      rw [out] at hy
      exact packOfUnpack y hy

end LogicLineages.PersistentMarking.NumberedWindowInternalSingletonBottom
