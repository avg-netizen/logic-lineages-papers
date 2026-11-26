module
public import LogicLineages.PermittedControl.ActualCountCoreLabelsTargets
import LogicLineages.PermittedControl.ActualCountCoreLabelsSyntaxProof
import LogicLineages.PermittedControl.ActualZeroClassReplacementPrefixProof
import LogicLineages.PermittedControl.CountTransferCoreProof
import LogicLineages.PermittedControl.SelectedCountOnlyClassProof
import LogicLineages.PermittedControl.FixedEntryClosedScanActualProof
import LogicLineages.PermittedControl.ShortFieldGapProof
import LogicLineages.PermittedControl.PreparedParameterActualProof
import LogicLineages.PermittedControl.FunnelProof
import LogicLineages.OrdinalComparison.OrdinalRepresentationSound

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCountCoreLabels
open OrdinalComparison FieldComparison PreparedProjection
open SelectedCountOnlyClass (prefixTarget prefixNotationExact)
open ActualZeroClassReplacement (exactPrefixRead)

private theorem longHasZeroShort (lam mu : NONote) (h : LongField (.entry 0 lam mu)) :
    shortGapLength lam mu = 0 := by
  have proper : ProperField (.entry 0 lam mu) := ⟨h.1,h.2.1,h.2.2.1⟩
  by_contra nonzero
  have positive : 0 < shortGapLength lam mu := Nat.pos_of_ne_zero nonzero
  exact h.2.2.2 ⟨shortGapLength lam mu,positive,
    (shortGapRecognition lam mu proper _ positive).2.2.mp rfl⟩

theorem exactPaidLongCountCoreLabel : ExactPaidLongCountCoreLabel := by
  intro f B selected ρ rank lam mu hLong paid eta x A
  have proper : ProperField (.entry 0 lam mu) := ⟨hLong.1,hLong.2.1,hLong.2.2.1⟩
  have affordable : actualOrdinalNorm lam.1.repr ≤ x := (le_max_left _ _).trans paid
  have zero := longHasZeroShort lam mu hLong
  have etaLiteral : eta.1.repr = mu.1.repr + Ordinal.omega0 ^ (2 : Ordinal.{0}) :=
    prefixNotationExact.2 mu
  have etaLimit : Order.IsSuccLimit eta.1.repr := by
    rw [etaLiteral]
    exact Ordinal.isSuccLimit_add _ square_facts.2.2
  obtain ⟨bound,i,k,hi,hk,orbit,twice⟩ :=
    countCore f B selected lam.1.repr mu.1.repr x (normalRepresentationSound lam)
      hLong.1 hLong.2.1 hLong.2.2.1 hLong.2.2.2 paid
  have prefixBound : eta.1.repr ≤ lam.1.repr := by simpa only [etaLiteral] using bound
  have first : FirstEntry f A eta.1.repr i := by simpa only [etaLiteral] using hi
  let q := entryNormAt f A i
  have actualCount : LowerOperandActual f ρ (.count rank lam mu) k := ⟨⟨proper,affordable⟩,hk⟩
  have literalCount : lowerOperandRead f ρ (.count rank lam mu) = some (some k) :=
    (preparedTiedProjection.1 f ρ _ k).mpr actualCount
  have literalPrefix : fixedEntryClosedScan f (rawNoteEncode lam.1,rawNoteEncode eta.1,x) =
      some (some (q,i)) :=
    ((fixedEntryClosedActual f lam eta x (.inr etaLimit)).1 q i).mpr ⟨first,rfl⟩
  have identity := (exactPrefixRead f ρ rank lam mu k i actualCount prefixBound first).1
  have classifier := exactCountCoreClassifier lam mu
  rcases prefixBound.eq_or_lt with eq | lt
  · let F := ValueField.iterate 1
    have iZero : i = 0 := identity.mpr eq
    have qBase : q = x := by
      change q = f^[i] x at orbit
      simpa [iZero] using orbit
    have classified := classifier.2.2.1 proper zero eq
    have field : fieldLabel lam mu = some F := by simp only [fieldLabel,classified,F]
    have fv : LowerOperandActual f ρ (.ordinary rank F) (f q) := by
      refine ⟨True.intro,?_⟩
      change f q = f^[1] x
      simp [qBase]
    exact ⟨F,i,k,q,field,fun impossible => False.elim ((ne_of_lt impossible) eq),
      fun _ => ⟨classified,rfl,iZero⟩,prefixBound,first,hk,rfl,orbit,literalPrefix,literalCount,
      True.intro,fv,(preparedTiedProjection.1 f ρ _ _).mpr fv,twice⟩
  · let F := ValueField.entry 1 lam eta
    have iPositive : 0 < i := Nat.pos_of_ne_zero (fun aiz => (ne_of_lt lt) (identity.mp aiz))
    have classified := classifier.2.2.2.1 proper zero lt
    have field : fieldLabel lam mu = some F := by simp only [fieldLabel,classified,F]
    have well : ProperField F := ⟨proper.1,.inr etaLimit,lt⟩
    have fv : LowerOperandActual f ρ (.ordinary rank F) (f q) := by
      refine ⟨⟨well,affordable⟩,i,first,?_⟩
      change f q = f^[1] q
      simp
    exact ⟨F,i,k,q,field,fun _ => ⟨classified,rfl,iPositive⟩,
      fun impossible => False.elim ((ne_of_lt lt) impossible),prefixBound,first,hk,rfl,orbit,
      literalPrefix,literalCount,well,fv,(preparedTiedProjection.1 f ρ _ _).mpr fv,twice⟩

end LogicLineages.PermittedControl.ActualCountCoreLabels
