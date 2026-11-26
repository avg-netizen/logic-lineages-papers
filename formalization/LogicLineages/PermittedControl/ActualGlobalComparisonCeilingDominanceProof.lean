module
public import LogicLineages.PermittedControl.ActualGlobalComparisonCeilingTargets
import LogicLineages.PermittedControl.ActualSyntaxChargeBudgetProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualGlobalComparisonCeiling
open ActualFullValueLabels (Label labels operandLabel activeLabel)
open ActualFullLabelPairGuards (Pair cost)
open ActualFiniteFullValueGuards (pairs familyCost)
open ActualFiniteGlobalTail (globalAlphabet syntaxCharge)
open ActualSyntaxChargeBudget (syntaxBudget exactChargeBudget)
open PreparedProjection (LowerOperand)
open MixedSameRankResidue (WeightedOperand)

theorem labelOrigin (ts : List WeightedOperand) (l : Label) (h : l ∈ labels ts) :
    ∃ t ∈ ts, operandLabel t.2 = some l ∧ l.rank = t.2.rank := by
  obtain ⟨t,ht,chosen⟩ := List.mem_filterMap.mp h
  have nz : t.1 ≠ 0 := by
    intro zero
    simp [activeLabel,zero] at chosen
  have same : operandLabel t.2 = some l := by simpa only [activeLabel,if_neg nz] using chosen
  refine ⟨t,ht,same,?_⟩
  generalize ho : t.2 = op at same ⊢
  cases op with
  | coordinate _ => cases same
  | ordinary rank field =>
      cases field with
      | iterate n =>
          cases n with
          | zero => cases same
          | succ k => exact (congrArg Label.rank (Option.some.inj same)).symm
      | entry k lam mu => exact (congrArg Label.rank (Option.some.inj same)).symm
  | count rank lam mu =>
      cases result : ActualCountCoreLabels.fieldLabel lam mu with
      | none => simp [operandLabel,result] at same
      | some F =>
          have fact : (some (⟨rank,F⟩ : Label)) = some l := by
            simpa only [operandLabel,result,Option.map_some] using same
          exact (congrArg Label.rank (Option.some.inj fact)).symm

private theorem pairMap (ls : List Label) (p : Pair) :
    p ∈ pairs ls ↔ p.1 ∈ ls ∧ p.2 ∈ ls := by
  constructor
  · intro good
    obtain ⟨l,hl,inRow⟩ := List.mem_flatMap.mp good
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp inRow
    exact ⟨hl,hr⟩
  · rintro ⟨left,right⟩
    exact List.mem_flatMap.mpr ⟨p.1,left,List.mem_map.mpr ⟨p.2,right,rfl⟩⟩

private theorem maxMember {α : Type} (w : α → Nat) (xs : List α) (x : α) (hx : x ∈ xs) :
    w x ≤ xs.foldr (fun a k => max (w a) k) 0 := by
  induction xs with
  | nil => cases hx
  | cons a xs ih =>
      rcases List.mem_cons.mp hx with eq | tail
      · subst a
        exact le_max_left _ _
      · exact (ih tail).trans (le_max_right _ _)

private theorem maxDominance {α : Type} (w : α → Nat) (xs : List α) (bound : Nat)
    (paid : ∀ a ∈ xs, w a ≤ bound) : xs.foldr (fun a k => max (w a) k) 0 ≤ bound := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons a xs ih =>
      exact max_le (paid a List.mem_cons_self)
        (ih (fun q inTail => paid q (List.mem_cons_of_mem _ inTail)))

private theorem familyMono (B : Nat) (ls rs : List Label) (subset : ∀ l ∈ ls, l ∈ rs) :
    familyCost B ls ≤ familyCost B rs := by
  apply maxDominance
  intro p hp
  obtain ⟨left,right⟩ := (pairMap ls p).mp hp
  exact maxMember (cost B) (pairs rs) p ((pairMap rs p).mpr
    ⟨subset p.1 left,subset p.2 right⟩)

theorem exactAlphabetComparisonDominance : ExactAlphabetComparisonDominance := by
  constructor
  · intro B ts alphabet subset
    apply familyMono
    intro l used
    obtain ⟨t,ht,fromTerm,_⟩ := labelOrigin ts l used
    exact List.mem_filterMap.mpr ⟨t.2,subset t ht,fromTerm⟩
  · intro B r ts
    apply familyMono
    intro l has
    obtain ⟨op,old,eq⟩ := List.mem_filterMap.mp has
    obtain ⟨n,hn,read⟩ := List.mem_flatMap.mp old
    have upto : n < syntaxBudget r ts + 1 :=
      (List.mem_range.mp hn).trans_le (Nat.succ_le_succ (exactChargeBudget.2.1 r ts))
    exact List.mem_filterMap.mpr ⟨op,
      List.mem_flatMap.mpr ⟨n,List.mem_range.mpr upto,read⟩,eq⟩

end LogicLineages.PermittedControl.ActualGlobalComparisonCeiling
