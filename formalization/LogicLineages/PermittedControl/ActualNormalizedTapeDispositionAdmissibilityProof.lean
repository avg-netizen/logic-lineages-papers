module
public import LogicLineages.PermittedControl.ActualNormalizedTapeDispositionTargets
import LogicLineages.PermittedControl.ActualNormalizedTapeSelectedCountKeysProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualNormalizedTapeDisposition
open OrdinalComparison FieldComparison PreparedProjection
open ActualMixedRowLeadingAnnotations ActualZeroClassReplacement ActualWeightedReadNormalization
open ActualRankedRowColumns ActualRankedZeroClass ActualCountOriginDispositions
open ActualZeroClassGroupedMovedCount ActualZeroClassSelectedCountKeys ActualZeroClassCohortTransfer
open ActualZeroClassSelectedDispositionSums
open SelectedCountOnlyClass (prefixTarget)

open ActualNormalizedTape ActualNormalizedTapeSelectedCountKeys

private theorem lookupOnOriginal {r : Nat} (indexed : List (KeyedDisposition r))
    (unique : (indexed.map Prod.fst).Nodup) (item : KeyedDisposition r)
    (member : item ∈ indexed) :
    dispositionAt indexed item.1 = item.2 := by
  induction indexed with
  | nil => simp at member
  | cons head tail ih =>
      have nodup : (head.1 :: tail.map Prod.fst).Nodup := unique
      obtain ⟨fresh,ntail⟩ := List.nodup_cons.mp nodup
      rcases List.mem_cons.mp member with equal | among
      · subst item
        simp [dispositionAt]
      · have ne : item.1 ≠ head.1 := by
          intro eq
          exact fresh (List.mem_map.mpr ⟨item,among,eq⟩)
        simp only [dispositionAt,if_neg ne]
        exact ih ntail among

private theorem outcomeAdmissible (f : Nat → Nat) (ρ : Nat → Nat) {r : Nat}
    (anchor : Option SurvivingPrefix) (x₀ : Fin r) (q : NONote × NONote)
    (anchorAt : AnchorAt anchor x₀ q) (entry : Origin) (d : CountDisposition)
    (out : List Read) (row : RankedRow r) (item : KeyedDisposition r)
    (matched : KeyedMatch row (entry,d) item)
    (outcome : OriginOutcome f ρ anchor entry d out) :
    item.2.Admissible x₀ item.1.2 := by
  rw [← matched.2.2]
  have sourceRank : entry.1.1.2.rank = item.1.2.val :=
    congrArg LowerOperand.rank matched.1
  obtain ⟨⟨⟨a,op⟩,v⟩,ann⟩ := entry
  cases op <;> cases ann <;> simp only [OriginOutcome] at outcome
  all_goals try exact outcome.2.elim
  rename_i rank lam mu i E κ
  change rank = item.1.2.val at sourceRank
  have head := outcome.2
  by_cases identity : i = 0
  · simp only [if_pos identity] at head
    obtain ⟨_,rfl,_⟩ := head
    exact True.intro
  · by_cases long : shortGapLength lam (prefixTarget mu) = 0
    · simp only [if_neg identity,if_pos long] at head
      obtain ⟨pivot,hp,_,_,tail⟩ := head
      have calibrated : pivot.rank = x₀.val := (anchorAt pivot hp).1
      by_cases same : rank = pivot.rank
      · simp only [if_pos same] at tail
        obtain ⟨_,rfl,_⟩ := tail
        exact Fin.ext (sourceRank.symm.trans (same.trans calibrated))
      · simp only [if_neg same] at tail
        obtain ⟨strict,_,_,_,rfl,_⟩ := tail
        change x₀.val < item.1.2.val
        calc
          x₀.val = pivot.rank := calibrated.symm
          _ < rank := strict
          _ = item.1.2.val := sourceRank
    · simp only [if_neg identity,if_neg long] at head
      obtain ⟨_,rfl,_⟩ := head
      exact True.intro

private theorem ledgerAdmissible (f : Nat → Nat) (ρ : Nat → Nat) {r : Nat}
    (anchor : Option SurvivingPrefix) (x₀ : Fin r) (q : NONote × NONote)
    (anchorAt : AnchorAt anchor x₀ q) (row : RankedRow r)
    (origins : List Origin) (ledger : List DispositionEntry) (out : List Read)
    (disposed : DisposedOrigins f ρ anchor origins ledger out) :
    ∀ (indexed : List (KeyedDisposition r)),
      List.Forall₂ (KeyedMatch row) ledger indexed →
      ∀ item ∈ indexed, item.2.Admissible x₀ item.1.2 := by
  induction disposed with
  | nil =>
      intro indexed matched
      cases matched
      simp
  | @cons entry _ d _ first _ outcome _ ih =>
      intro indexed matched
      cases matched with
      | cons head tail =>
          intro item member
          rcases List.mem_cons.mp member with equal | among
          · subst item
            exact outcomeAdmissible f ρ anchor x₀ q anchorAt entry d first row _ head outcome
          · exact ih _ tail item among

theorem exactTapeDispositionAdmissibility : ExactTapeDispositionAdmissibility := by
  intro f ρ C r constant raw xs annotations x₀ q ledger moved bounded tape aligned present
  dsimp only
  intro anchorAt disposed
  let anchor := leastPrefix (cohort f C (xs.map Prod.fst) annotations)
  let row := rankedRow r constant raw
  let indexed := keyedLedger r ledger
  let S := (finiteClassColumns r (classReads f C xs annotations)).2
  obtain ⟨_,matched,unique,keys⟩ :=
    exactTapeSelectedCountKeyLedger f ρ C r constant raw xs annotations ledger moved
      bounded tape aligned present disposed
  have hready := ledgerAdmissible f ρ anchor x₀ q anchorAt row _ ledger moved disposed indexed matched
  intro k hk
  have hkey : k ∈ keyedSet indexed := by rw [keys]; exact hk
  have hmap : k ∈ indexed.map Prod.fst := by
    classical
    simpa only [keyedSet,List.mem_toFinset] using hkey
  obtain ⟨item,member,hk'⟩ := List.mem_map.mp hmap
  have hlookup : dispositionAt indexed k = item.2 :=
    hk' ▸ lookupOnOriginal indexed unique item member
  rw [hlookup,← hk']
  exact hready item member

end LogicLineages.PermittedControl.ActualNormalizedTapeDisposition
