module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionRawProof
open Source NumberedAuxiliaryCoding OriginalRawSyntaxTransport

theorem variableCommute {Symbol : Type} (alpha beta : Ty) (i j x : Nat) (hij : i < j) :
    eraseCode alpha i (eraseCode beta j (Code.var x : Code Symbol)) =
      eraseCode beta (j - 1) (eraseCode alpha i (.var x)) := by
  by_cases hxi : x < i
  · have hxj : x < j := by omega
    have hxjm : x < j - 1 := by omega
    simp [eraseCode,hxi,hxj,hxjm]
  · by_cases hxe : x = i
    · subst x
      have hj : ¬ i < i := by omega
      simp [eraseCode,hij,hj]
    · by_cases hxj : x < j
      · have hxm : x - 1 < j - 1 := by omega
        simp [eraseCode,hxi,hxe,hxj,hxm]
      · by_cases hxje : x = j
        · subst x
          have hji : ¬ j < i := by omega
          have hne : j ≠ i := by omega
          simp [eraseCode,hji,hne]
        · have hmi : ¬ x - 1 < i := by omega
          have hmei : x - 1 ≠ i := by omega
          have hmj : ¬ x - 1 < j - 1 := by omega
          have hmej : x - 1 ≠ j - 1 := by omega
          simp [eraseCode,hxi,hxe,hxj,hxje,hmi,hmei,hmj,hmej]

theorem commute {Symbol : Type} (q : Code Symbol) :
    ∀ (alpha beta : Ty) (i j : Nat), i < j →
      eraseCode alpha i (eraseCode beta j q) =
        eraseCode beta (j - 1) (eraseCode alpha i q) := by
  induction q with
  | var x => intro alpha beta i j h; exact variableCommute alpha beta i j x h
  | lam sigma q ih =>
    intro alpha beta i j h
    have hs : i + 1 < j + 1 := by omega
    have hj : j - 1 + 1 = j := by omega
    simpa only [eraseCode,Nat.add_sub_cancel,hj] using congrArg (Code.lam sigma) (ih alpha beta (i+1) (j+1) hs)
  | app sigma q a ihq iha =>
    intro alpha beta i j h
    simp only [eraseCode,ihq alpha beta i j h,iha alpha beta i j h]
  | bottom tau => intros; rfl
  | ordinary head base ih =>
    intro alpha beta i j h
    simp only [eraseCode,ih alpha beta i j h]
  | numbered label head tau base types extras ihb ihe =>
    intro alpha beta i j h
    simp only [eraseCode,ihb alpha beta i j h,ihe alpha beta i j h]
  | argumentsNil => intros; rfl
  | argumentsCons sigma q rest ihq ihr =>
    intro alpha beta i j h
    simp only [eraseCode,ihq alpha beta i j h,ihr alpha beta i j h]

theorem actualRawCommutation : OriginalTwoDeletionTargets.RawCommutation := by
  intro Symbol alpha beta i j h q
  exact commute q alpha beta i j h

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionRawProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionRawProof
