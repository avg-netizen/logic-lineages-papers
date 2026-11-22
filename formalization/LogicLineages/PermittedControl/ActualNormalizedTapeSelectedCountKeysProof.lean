module
public import LogicLineages.PermittedControl.ActualNormalizedTapeSelectedCountKeysTargets
import LogicLineages.PermittedControl.ActualNormalizedTapeCertificateProof
import LogicLineages.PermittedControl.ActualNormalizedTapeClassProof
import LogicLineages.PermittedControl.ActualRankedZeroClassSelectionProof
import LogicLineages.PermittedControl.ActualRankedZeroClassFiniteProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualNormalizedTapeSelectedCountKeys
open OrdinalComparison PreparedProjection
open ActualMixedRowLeadingAnnotations ActualZeroClassReplacement ActualWeightedReadNormalization
open ActualRankedRowColumns ActualRankedZeroClass ActualCountOriginDispositions ActualZeroClassCohortTransfer

open ActualNormalizedTape ActualZeroClassSelectedCountKeys

private theorem originalOrder (f : Nat → Nat) (ρ : Nat → Nat) (anchor : Option SurvivingPrefix)
    (origins : List Origin) (ledger : List DispositionEntry) (out : List Read)
    (disposed : DisposedOrigins f ρ anchor origins ledger out) :
    ledger.map Prod.fst = origins := by
  induction disposed with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons,ih]

private theorem countedShape (f : Nat → Nat) (ρ : Nat → Nat) (C : Nat) (o : Origin)
    (actual : ActualAnnotation f ρ o.1.1 o.1.2 o.2) (full : fullValue f o.2 = some C) :
    isCountAnnotation o.2 = true ↔
      ∃ n lam mu, o.1.1.2 = LowerOperand.count n lam mu := by
  obtain ⟨rd,ann⟩ := o
  cases ann with
  | zeroWeight => cases full
  | linear => cases full
  | ordinary q =>
      obtain ⟨_,rank,F,hfield,_,_,_⟩ := actual
      constructor
      · intro h; cases h
      · rintro ⟨n,lam,mu,hcount⟩
        have bad : LowerOperand.ordinary rank F = LowerOperand.count n lam mu :=
          hfield.symm.trans hcount
        cases bad
  | count i q κ =>
      obtain ⟨_,rank,lam,mu,hfield,_⟩ := actual
      exact ⟨fun _ => ⟨rank,lam,mu,hfield⟩,fun _ => rfl⟩

private theorem keyedMatchAll {r : Nat} (row : RankedRow r) (ledger : List DispositionEntry)
    (known : ∀ item ∈ ledger, ∃ k,
      finiteClassKey r item.1.1.1.2 = some (.inr k) ∧
      item.1.1.1.2 = countOperand r k ∧ item.1.1.1.1 = row.count k) :
    List.Forall₂ (KeyedMatch row) ledger (keyedLedger r ledger) := by
  induction ledger with
  | nil => exact .nil
  | cons item ledger ih =>
      obtain ⟨k,found,op,wt⟩ := known item List.mem_cons_self
      have htail := ih (fun a ha => known a (List.mem_cons_of_mem _ ha))
      have he : keyedLedger r (item::ledger) = (k,item.2)::keyedLedger r ledger := by
        simp only [keyedLedger,List.filterMap_cons,found]
      rw [he]
      exact .cons ⟨op,wt,rfl⟩ htail

private theorem keyedOperandOrder {r : Nat} (row : RankedRow r) (ledger : List DispositionEntry)
    (indexed : List (KeyedDisposition r))
    (matched : List.Forall₂ (KeyedMatch row) ledger indexed) :
    indexed.map (fun kd => countOperand r kd.1) = ledger.map (fun item => item.1.1.1.2) := by
  induction matched with
  | nil => rfl
  | cons h _ ih => simp only [List.map_cons,ih,h.1]

theorem exactTapeSelectedCountKeyLedger : ExactTapeSelectedCountKeyLedger := by
  classical
  intro f ρ C r constant raw xs annotations ledger moved bounded tape aligned present
  dsimp only
  intro disposed
  let anchor := leastPrefix (cohort f C (xs.map Prod.fst) annotations)
  let row := rankedRow r constant raw
  let selected := classReads f C xs annotations
  let origins := countOrigins f C xs annotations
  let indexed := keyedLedger r ledger
  have horder : ledger.map Prod.fst = origins := originalOrder f ρ anchor origins ledger moved disposed
  have hcolumns := exactTapeRankedMembers f ρ raw xs r constant bounded tape
  have hnodup := tape.unique
  have hselected := exactClassSelection f ρ C xs annotations aligned
  have hclass := exactTapeRankedClass f ρ r constant raw xs annotations C bounded tape aligned present
  have originsSub : (origins.map Prod.fst).Sublist selected := by
    exact (List.filter_sublist (p := fun o => isCountAnnotation o.2)
      (l := classLedger f C xs annotations)).map Prod.fst
  have hcounts (o : Origin) (ho : o ∈ origins) :
      ∃ rank lam mu, o.1.1.2 = LowerOperand.count rank lam mu := by
    obtain ⟨hclassMem,hkind⟩ := List.mem_filter.mp ho
    obtain ⟨ha,hfull⟩ := hselected.2.1 o hclassMem
    exact (countedShape f ρ C o ha hfull).mp hkind
  have allKnown (item : DispositionEntry) (hm : item ∈ ledger) :
      ∃ k, finiteClassKey r item.1.1.1.2 = some (.inr k) ∧
        item.1.1.1.2 = countOperand r k ∧ item.1.1.1.1 = row.count k := by
    have ho : item.1 ∈ origins := horder ▸ List.mem_map.mpr ⟨item,hm,rfl⟩
    have hs : item.1.1 ∈ selected := originsSub.subset (List.mem_map.mpr ⟨item.1,ho,rfl⟩)
    have col := hcolumns item.1.1 (hselected.1.subset hs)
    obtain ⟨rank,lam,mu,hshape⟩ := hcounts item.1 ho
    have hcharged : NonlinearOperand item.1.1.1.2 := by rw [hshape]; trivial
    obtain ⟨key,hkey,facts⟩ := chargedKey row item.1.1 hcharged col
    cases key with
    | inl k =>
        have bad := facts.1
        rw [hshape] at bad
        change LowerOperand.count rank lam mu = LowerOperand.ordinary k.1 k.2 at bad
        cases bad
    | inr k =>
        exact ⟨k,hkey,facts.1,by simpa only [leadingWeight,hshape] using facts.2.2⟩
  have hmatch : List.Forall₂ (KeyedMatch row) ledger indexed := keyedMatchAll row ledger allKnown
  have hmaps := keyedOperandOrder row ledger indexed hmatch
  have hrawKeys :
      ledger.map (fun item => item.1.1.1.2) = (origins.map Prod.fst).map (fun rd => rd.1.2) := by
    calc
      _ = ((ledger.map Prod.fst).map Prod.fst).map (fun rd => rd.1.2) := by
        simp only [List.map_map,Function.comp_def]
      _ = _ := by rw [horder]
  have hflatten : (indexed.map Prod.fst).map (countOperand r) =
      indexed.map (fun kd => countOperand r kd.1) := by
    simp only [List.map_map,Function.comp_def]
  have hnd : (indexed.map Prod.fst).Nodup := by
    apply List.Nodup.of_map (countOperand r)
    rw [hflatten,hmaps,hrawKeys]
    exact ((originsSub.trans hselected.1).map _).nodup hnodup
  refine ⟨horder,hmatch,hnd,?_⟩
  apply Finset.ext
  intro k
  simp only [keyedSet,List.mem_toFinset]
  constructor
  · intro hk
    have hmem : countOperand r k ∈ indexed.map (fun kd => countOperand r kd.1) := by
      rw [← hflatten]
      exact List.mem_map.mpr ⟨k,hk,rfl⟩
    rw [hmaps,hrawKeys] at hmem
    obtain ⟨rd,hrd,he⟩ := List.mem_map.mp hmem
    exact (hclass.2.2.2.2.1 k).mpr ⟨rd,originsSub.subset hrd,he⟩
  · intro hk
    obtain ⟨rd,hrd,he⟩ := (hclass.2.2.2.2.1 k).mp hk
    obtain ⟨o,ho,hro⟩ := List.mem_map.mp hrd
    have hop : o.1.1.2 = countOperand r k :=
      (congrArg (fun p : Read => p.1.2) hro).trans he
    obtain ⟨ha,hfull⟩ := hselected.2.1 o ho
    have hcount : isCountAnnotation o.2 = true :=
      (countedShape f ρ C o ha hfull).mpr ⟨k.2,k.1.1,k.1.2,hop⟩
    have horig : o ∈ origins := List.mem_filter.mpr ⟨ho,hcount⟩
    have hmem : countOperand r k ∈ indexed.map (fun kd => countOperand r kd.1) := by
      rw [hmaps,hrawKeys]
      exact List.mem_map.mpr ⟨o.1,List.mem_map.mpr ⟨o,horig,rfl⟩,hop⟩
    rw [← hflatten] at hmem
    obtain ⟨j,hj,hjk⟩ := List.mem_map.mp hmem
    exact (countOperand r).injective hjk ▸ hj

end LogicLineages.PermittedControl.ActualNormalizedTapeSelectedCountKeys
