module
public import LogicLineages.PermittedControl.ActualCanonicalOperandGroupingTargets
import LogicLineages.PermittedControl.ActualCanonicalOperandGroupingTapeProof
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationActualProof
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationWeightsProof
import LogicLineages.PermittedControl.PreparedParameterActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalOperandGrouping
open scoped Classical
open PreparedProjection ActualZeroClassReplacement
open ActualWeightedReadNormalization

private theorem keyPerm (xs : List Read) :
    ((groupTyped (xs.map Prod.fst)).map Prod.snd).Perm (groupedWeights xs).support.toList := by
  have facts := exactCanonicalTape
  apply (List.perm_ext_iff_of_nodup (facts.2.1 _) (Finset.nodup_toList _)).mpr
  intro key
  constructor
  · intro listed
    obtain ⟨⟨w,op⟩,member,same⟩ := List.mem_map.mp listed
    change op = key at same
    subst op
    exact Finset.mem_toList.mpr ((facts.2.2 xs w key).mp member).2
  · intro member
    let w := groupedWeights xs key
    exact List.mem_map.mpr ⟨(w,key),(facts.2.2 xs w key).mpr
      ⟨rfl,Finset.mem_toList.mp member⟩,rfl⟩

private theorem allSourceHit (f ρ : Nat → Nat) (xs : List Read)
    (ok : liftedReads f ρ xs) (rd : Read) (used : rd ∈ xs) :
    lowerOperandRead f ρ rd.1.2 = some (some rd.2) :=
  List.all_eq_true.mp ((exactInputChecks f ρ xs).mpr ok) rd used |> of_decide_eq_true

private noncomputable def payload (f ρ : Nat → Nat) (op : LowerOperand) : Nat :=
  (lowerOperandRead f ρ op).join.getD 0

private noncomputable def render (f ρ : Nat → Nat) (xs : List Read) (key : LowerOperand) : Read :=
  ((groupedWeights xs key,key),payload f ρ key)

private theorem mapActual (f ρ : Nat → Nat) (xs : List Read) (ok : liftedReads f ρ xs)
    (keys : List LowerOperand) (active : ∀ key ∈ keys, key ∈ (groupedWeights xs).support) :
    keys.mapM (readAtWeight f ρ (groupedWeights xs)) = some (keys.map (render f ρ xs)) := by
  induction keys with
  | nil => rfl
  | cons key keys ih =>
      obtain ⟨rd,used,same⟩ := (exactGroupedWeights xs key).2.2 (active key List.mem_cons_self)
      have hit := allSourceHit f ρ xs ok rd used
      rw [same] at hit
      have head : readAtWeight f ρ (groupedWeights xs) key = some (render f ρ xs key) := by
        simp [readAtWeight,render,payload,hit]
      have tail := ih (fun k listed => active k (List.mem_cons_of_mem _ listed))
      simp [List.mapM_cons,head,tail]

private theorem renderedTerms (f ρ : Nat → Nat) (xs : List Read) :
    (((groupTyped (xs.map Prod.fst)).map Prod.snd).map (render f ρ xs)).map Prod.fst =
      groupTyped (xs.map Prod.fst) := by
  simp only [List.map_map]
  conv_rhs => rw [← List.map_id (groupTyped (xs.map Prod.fst))]
  apply List.map_congr_left
  intro t member
  exact Prod.ext ((exactCanonicalTape.2.2 xs t.1 t.2).mp
    (show (t.1,t.2) ∈ groupTyped (xs.map Prod.fst) from member)).1.symm rfl

private theorem allHitOfPerm (f ρ : Nat → Nat) (out old : List Read) (same : out.Perm old)
    (live : liftedReads f ρ old) : liftedReads f ρ out := by
  apply (exactInputChecks f ρ out).mp
  apply List.all_eq_true.mpr
  intro rd member
  exact List.all_eq_true.mp ((exactInputChecks f ρ old).mpr live) rd (same.mem_iff.mp member)

private theorem readSumOfPerm (out old : List Read) (same : out.Perm old) :
    readSum out = readSum old := by
  induction same with
  | nil => rfl
  | cons rd perm ih =>
      change rd.1.1 * (rd.2 : Int) + readSum _ = rd.1.1 * (rd.2 : Int) + readSum _
      rw [ih]
  | swap a b rest =>
      change b.1.1 * (b.2 : Int) + (a.1.1 * (a.2 : Int) + readSum rest) =
        a.1.1 * (a.2 : Int) + (b.1.1 * (b.2 : Int) + readSum rest)
      exact add_left_comm _ _ _
  | trans left right ihLeft ihRight => exact ihLeft.trans ihRight

theorem exactCanonicalReads : ExactCanonicalReads := by
  intro f ρ xs
  let keys := (groupTyped (xs.map Prod.fst)).map Prod.snd
  let out := keys.map (render f ρ xs)
  let usual := (groupedWeights xs).support.toList
  have perm : keys.Perm usual := keyPerm xs
  have usualHit (ok : liftedReads f ρ xs) :
      normalizeReads f ρ xs = some (usual.map (render f ρ xs)) := by
    simp only [normalizeReads,(exactInputChecks f ρ xs).mpr ok,if_true]
    exact mapActual f ρ xs ok usual (fun key included => Finset.mem_toList.mp included)
  have hit (ok : liftedReads f ρ xs) :
      normalizeCanonical f ρ xs = some out := by
    simp only [normalizeCanonical,(exactInputChecks f ρ xs).mpr ok,if_true]
    exact mapActual f ρ xs ok keys (fun key included => Finset.mem_toList.mp (perm.mem_iff.mp included))
  refine ⟨?_,?_⟩
  · constructor
    · intro failure live
      rw [hit live] at failure
      cases failure
    · intro invalid
      have checked : checkedReads f ρ xs = false := by
        cases h : checkedReads f ρ xs with
        | false => rfl
        | true => exact False.elim (invalid ((exactInputChecks f ρ xs).mp h))
      simp only [normalizeCanonical,checked,if_false,Bool.false_eq_true]
  · intro old oldEq
    have live : liftedReads f ρ xs := by
      by_contra missing
      have absent := (exactNormalizedReads f ρ xs).1.mpr missing
      rw [oldEq] at absent
      cases absent
    obtain ⟨ys,eq,_,_,ysLive,ysValue,_⟩ := (exactNormalizedReads f ρ xs).2 live
    have ysOld : ys = old := Option.some.inj (eq.symm.trans oldEq)
    have oldRender : usual.map (render f ρ xs) = old := Option.some.inj ((usualHit live).symm.trans oldEq)
    have same : out.Perm old := oldRender ▸ perm.map (render f ρ xs)
    exact ⟨out,hit live,same,renderedTerms f ρ xs,allHitOfPerm f ρ out old same (ysOld ▸ ysLive),
      (readSumOfPerm out old same).trans ((ysOld ▸ ysValue).symm)⟩

end LogicLineages.PermittedControl.ActualCanonicalOperandGrouping
