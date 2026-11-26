module
public import LogicLineages.PermittedControl.StageCallbackLevelOrderTargets
import LogicLineages.PermittedControl.StageCallbackCanonicalRoutesLayoutProof
import LogicLineages.PermittedControl.StageCallbackCanonicalSupplierProof
import LogicLineages.PermittedControl.StageCallbackSupplierContractProof

@[expose] public section
namespace LogicLineages.PermittedControl.StageCallbackLevelOrder
open OrdinalComparison
open StageCallbackSupplier (Supplier SupplierShape SupplierExact stageChildren Emits
  exactSuppliedStageCallback)
open StageCallbackCanonicalRoutes (CanonicalActive tapes guard routes linearRoute signedRoute
  exactCanonicalRouteLayout)
open StageCallbackCanonicalSupplier (canonical exactCanonicalSupplierShape
  exactCanonicalSupplierExact)
open ActualCanonicalOperandGrouping (groupTyped)
open ActualCanonicalSymbolicZeroSuccessor (canonicalSuccessor)
open ActualCanonicalTerminalTruth (canonicalPacket)
open ActualFullLabelPairGuards (Answer)
open ActualFullValueMaximalMetadata (maximalCoefficient)
open ActualSymbolicZeroSuccessor (SyntaxState)
open ActualSignedOrdinaryPairHigh (OrderTest)
open ActualInitialSignedCountCleanup (cleanup)
open ActualPreparedSlotAppend (Packet)
open ActualBoundedSignedRoutes (Route prefixGuard)
open ActualSelectedSignedRoutePacket (packet)
open ActualPaidMixedMatrixTuples (MixedRow)
open ActualSyntaxChargeBudget (syntaxBudget)

/-- A route read below a prefix of guards already met. -/
def pfx (pre : List Packet) (ρ : Route) : Route := ⟨pre ++ ρ.guards,ρ.tip⟩

theorem pfx_nil (ρ : Route) : pfx [] ρ = ρ := by
  cases ρ
  rfl

/-- The frontier grown from an arbitrary list of entries. -/
noncomputable def grow (top : Nat) (es : List Entry) : Nat → List Entry
  | 0 => es
  | n+1 => (grow top es n).flatMap (children top)

theorem level_eq_grow (top : Nat) (s : SyntaxState) (n : Nat) :
    level top s n = grow top [([],s)] n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show (level top s n).flatMap (children top) = (grow top [([],s)] n).flatMap (children top)
      rw [ih]

/-- First-step decomposition of the frontier of one entry. -/
theorem mem_grow_succ (top : Nat) (e : Entry) (n : Nat) :
    ∀ x : Entry, x ∈ grow top [e] (n+1) ↔ ∃ c ∈ children top e, x ∈ grow top [c] n := by
  induction n with
  | zero =>
      intro x
      constructor
      · intro h
        obtain ⟨y,hy,hx⟩ := List.mem_flatMap.mp h
        have same : y = e := List.mem_singleton.mp hy
        rw [same] at hx
        exact ⟨x,hx,List.mem_singleton.mpr rfl⟩
      · rintro ⟨c,hc,hx⟩
        have same : x = c := List.mem_singleton.mp hx
        rw [same]
        exact List.mem_flatMap.mpr ⟨e,List.mem_singleton.mpr rfl,hc⟩
  | succ n ih =>
      intro x
      constructor
      · intro h
        obtain ⟨y,hy,hx⟩ := List.mem_flatMap.mp h
        obtain ⟨c,hc,hy'⟩ := (ih y).mp hy
        exact ⟨c,hc,List.mem_flatMap.mpr ⟨y,hy',hx⟩⟩
      · rintro ⟨c,hc,h⟩
        obtain ⟨y,hy,hx⟩ := List.mem_flatMap.mp h
        exact List.mem_flatMap.mpr ⟨y,(ih y).mpr ⟨c,hc,hy⟩,hx⟩

theorem stepOf_zero (top : Nat) (pre : List Packet) (s : SyntaxState) (a : List Answer)
    (h : maximalCoefficient (groupTyped s.terms) a = 0) :
    stepOf top (pre,s) a = (canonicalSuccessor s.constant s.terms a).map
      (fun out => (pre ++ [guard top (groupTyped s.terms) a],out)) := if_pos h

theorem stepOf_nonzero (top : Nat) (pre : List Packet) (s : SyntaxState) (a : List Answer)
    (h : ¬ maximalCoefficient (groupTyped s.terms) a = 0) :
    stepOf top (pre,s) a = none := if_neg h

theorem leafOf_zero (top : Nat) (pre : List Packet) (s : SyntaxState) (a : List Answer)
    (h : maximalCoefficient (groupTyped s.terms) a = 0) :
    leafOf top (pre,s) a = none := if_pos h

theorem leafOf_nonzero (top : Nat) (pre : List Packet) (s : SyntaxState) (a : List Answer)
    (h : ¬ maximalCoefficient (groupTyped s.terms) a = 0) :
    leafOf top (pre,s) a = some ⟨pre ++ [guard top (groupTyped s.terms) a],
      .signed (maximalCoefficient (groupTyped s.terms) a)⟩ := if_neg h

theorem children_active (top : Nat) (pre : List Packet) (s : SyntaxState)
    (h : CanonicalActive top s.terms) :
    children top (pre,s) = (tapes (groupTyped s.terms)).filterMap (stepOf top (pre,s)) :=
  if_pos h

theorem children_idle (top : Nat) (pre : List Packet) (s : SyntaxState)
    (h : ¬ CanonicalActive top s.terms) : children top (pre,s) = [] := if_neg h

theorem leaves_active (top : Nat) (test : OrderTest) (positive : Bool) (pre : List Packet)
    (s : SyntaxState) (h : CanonicalActive top s.terms) :
    leaves top test positive (pre,s) =
      (tapes (groupTyped s.terms)).filterMap (leafOf top (pre,s)) := if_pos h

theorem leaves_idle (top : Nat) (test : OrderTest) (positive : Bool) (pre : List Packet)
    (s : SyntaxState) (h : ¬ CanonicalActive top s.terms) :
    leaves top test positive (pre,s) =
      [⟨pre,.linear (canonicalPacket top s.constant s.terms test.test positive)⟩] := if_neg h

theorem pfx_linear (top : Nat) (test : OrderTest) (positive : Bool) (pre : List Packet)
    (s : SyntaxState) :
    pfx pre (linearRoute top test positive s) =
      ⟨pre,.linear (canonicalPacket top s.constant s.terms test.test positive)⟩ := by
  simp [pfx,linearRoute]

theorem pfx_signed (top : Nat) (pre : List Packet) (s : SyntaxState) (a : List Answer) :
    pfx pre (signedRoute top s a) = ⟨pre ++ [guard top (groupTyped s.terms) a],
      .signed (maximalCoefficient (groupTyped s.terms) a)⟩ := rfl

theorem pfx_step (pre : List Packet) (g : Packet) (tail : Route) :
    pfx pre (prefixGuard g tail) = pfx (pre ++ [g]) tail := by
  simp [pfx,prefixGuard]

/-- Leaves reachable within `n` level steps from an entry are exactly the
tree routes at fuel `n` from its syntax, read below its guards. -/
theorem reachLeaves (top : Nat) (test : OrderTest) (positive : Bool) :
    ∀ (n : Nat) (pre : List Packet) (s : SyntaxState) (route : Route),
      (∃ k, k ≤ n ∧ ∃ y ∈ grow top [(pre,s)] k, route ∈ leaves top test positive y) ↔
        ∃ ρ ∈ routes top test positive n s, route = pfx pre ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro pre s route
    constructor
    · rintro ⟨k,hk,y,hy,hleaf⟩
      cases k with
      | zero =>
          have ye : y = (pre,s) := List.mem_singleton.mp hy
          rw [ye] at hleaf
          by_cases active : CanonicalActive top s.terms
          · rw [leaves_active top test positive pre s active] at hleaf
            obtain ⟨a,ha,hl⟩ := List.mem_filterMap.mp hleaf
            by_cases zero : maximalCoefficient (groupTyped s.terms) a = 0
            · rw [leafOf_zero top pre s a zero] at hl
              cases hl
            · rw [leafOf_nonzero top pre s a zero] at hl
              have eq := Option.some.inj hl
              exact ⟨signedRoute top s a,
                (exactCanonicalRouteLayout top n test positive s _).mpr
                  (Or.inr ⟨active,a,ha,Or.inl ⟨zero,rfl⟩⟩),
                eq.symm.trans (pfx_signed top pre s a).symm⟩
          · rw [leaves_idle top test positive pre s active] at hleaf
            have eq := List.mem_singleton.mp hleaf
            exact ⟨linearRoute top test positive s,
              (exactCanonicalRouteLayout top n test positive s _).mpr (Or.inl ⟨active,rfl⟩),
              eq.trans (pfx_linear top test positive pre s).symm⟩
      | succ j =>
          obtain ⟨c,hc,hy'⟩ := (mem_grow_succ top (pre,s) j y).mp hy
          by_cases active : CanonicalActive top s.terms
          · rw [children_active top pre s active] at hc
            obtain ⟨a,ha,hstep⟩ := List.mem_filterMap.mp hc
            by_cases zero : maximalCoefficient (groupTyped s.terms) a = 0
            · rw [stepOf_zero top pre s a zero] at hstep
              cases produced : canonicalSuccessor s.constant s.terms a with
              | none =>
                  rw [produced] at hstep
                  cases hstep
              | some out =>
                  rw [produced] at hstep
                  have ce : (pre ++ [guard top (groupTyped s.terms) a],out) = c :=
                    Option.some.inj hstep
                  rw [← ce] at hy'
                  have depth : n = (n-1)+1 := by omega
                  obtain ⟨tail,htail,eq⟩ := (ih (n-1) (by omega)
                    (pre ++ [guard top (groupTyped s.terms) a]) out route).mp
                    ⟨j,by omega,y,hy',hleaf⟩
                  exact ⟨prefixGuard (guard top (groupTyped s.terms) a) tail,
                    (exactCanonicalRouteLayout top n test positive s _).mpr
                      (Or.inr ⟨active,a,ha,Or.inr ⟨zero,n-1,out,depth,produced,tail,htail,rfl⟩⟩),
                    eq.trans (pfx_step pre _ tail).symm⟩
            · rw [stepOf_nonzero top pre s a zero] at hstep
              cases hstep
          · rw [children_idle top pre s active] at hc
            cases hc
    · rintro ⟨ρ,hρ,rfl⟩
      rcases (exactCanonicalRouteLayout top n test positive s ρ).mp hρ with
        ⟨idle,rfl⟩ | ⟨active,a,ha,branches⟩
      · refine ⟨0,Nat.zero_le _,(pre,s),List.mem_singleton.mpr rfl,?_⟩
        rw [leaves_idle top test positive pre s idle,pfx_linear]
        exact List.mem_singleton.mpr rfl
      · rcases branches with ⟨nonzero,rfl⟩ | ⟨zero,k,out,depth,success,tail,htail,rfl⟩
        · refine ⟨0,Nat.zero_le _,(pre,s),List.mem_singleton.mpr rfl,?_⟩
          rw [leaves_active top test positive pre s active]
          exact List.mem_filterMap.mpr ⟨a,ha,
            (leafOf_nonzero top pre s a nonzero).trans (congrArg some (pfx_signed top pre s a).symm)⟩
        · obtain ⟨j,hj,y,hy,hleaf⟩ := (ih k (by omega)
            (pre ++ [guard top (groupTyped s.terms) a]) out
            (pfx (pre ++ [guard top (groupTyped s.terms) a]) tail)).mpr ⟨tail,htail,rfl⟩
          refine ⟨j+1,by omega,y,(mem_grow_succ top (pre,s) j y).mpr
            ⟨(pre ++ [guard top (groupTyped s.terms) a],out),?_,hy⟩,?_⟩
          · rw [children_active top pre s active]
            refine List.mem_filterMap.mpr ⟨a,ha,?_⟩
            rw [stepOf_zero top pre s a zero,success]
            rfl
          · rw [pfx_step]
            exact hleaf

theorem exactLevelOrderRoutes : ExactLevelOrderRoutes := by
  intro top test positive fuel s route
  have key := reachLeaves top test positive fuel [] s route
  constructor
  · intro h
    obtain ⟨k,hk,hroute⟩ := List.mem_flatMap.mp h
    obtain ⟨y,hy,hleaf⟩ := List.mem_flatMap.mp hroute
    rw [level_eq_grow] at hy
    obtain ⟨ρ,hρ,eq⟩ := key.mp ⟨k,Nat.lt_succ_iff.mp (List.mem_range.mp hk),y,hy,hleaf⟩
    rw [eq,pfx_nil]
    exact hρ
  · intro h
    obtain ⟨k,hk,y,hy,hleaf⟩ := key.mpr ⟨route,h,(pfx_nil route).symm⟩
    refine List.mem_flatMap.mpr ⟨k,List.mem_range.mpr (Nat.lt_succ_of_le hk),
      List.mem_flatMap.mpr ⟨y,?_,hleaf⟩⟩
    rw [level_eq_grow]
    exact hy

theorem signedMembers (r top : Nat) (src : SyntaxState) (test : OrderTest) (positive : Bool)
    (q : Packet) :
    q ∈ alternatives r top (.signed ⟨src,test,positive⟩) ↔
      q ∈ StageCallbackCanonicalSupplier.alternatives r top (.signed ⟨src,test,positive⟩) := by
  constructor
  · intro h
    obtain ⟨route,member,rfl⟩ := List.mem_map.mp h
    exact List.mem_map.mpr ⟨route,
      (exactLevelOrderRoutes top test positive (syntaxBudget r src.terms) src route).mp member,rfl⟩
  · intro h
    obtain ⟨route,member,rfl⟩ := List.mem_map.mp h
    exact List.mem_map.mpr ⟨route,
      (exactLevelOrderRoutes top test positive (syntaxBudget r src.terms) src route).mpr member,rfl⟩

theorem exactLevelOrderMembers : ExactLevelOrderMembers := by
  intro r top row q
  rcases row with ⟨⟨test,c,ts⟩,bit⟩
  cases test with
  | equalZero => exact signedMembers r top (cleanup ⟨c,ts⟩) .equalZero bit q
  | nonnegative => exact signedMembers r top (cleanup ⟨c,ts⟩) .nonnegative bit q
  | positive => exact signedMembers r top (cleanup ⟨c,ts⟩) .positive bit q
  | congruence m => exact Iff.rfl

theorem exactSupplierMemberTransfer : ExactSupplierMemberTransfer := by
  intro alt alt' same
  refine ⟨fun shaped r top row q used => shaped r top row q ((same r top row q).mp used),?_⟩
  intro f B rowwise r top baseline row z admitted strict scope lower high
  refine (rowwise r top baseline row z admitted strict scope lower high).trans ?_
  constructor
  · rintro ⟨q,used,holds⟩
    exact ⟨q,(same r top row q).mpr used,holds⟩
  · rintro ⟨q,used,holds⟩
    exact ⟨q,(same r top row q).mp used,holds⟩

theorem exactLevelOrderSupplierShape : ExactLevelOrderSupplierShape :=
  (exactSupplierMemberTransfer canonical levelOrder exactLevelOrderMembers).1
    exactCanonicalSupplierShape

theorem exactLevelOrderSupplierExact : ExactLevelOrderSupplierExact := by
  intro f B selected
  exact (exactSupplierMemberTransfer canonical levelOrder exactLevelOrderMembers).2 f B
    (exactCanonicalSupplierExact f B selected)

theorem exactLevelOrderStageCallback : ExactLevelOrderStageCallback := by
  intro f B selected high emits
  exact exactSuppliedStageCallback f B levelOrder exactLevelOrderSupplierShape
    (exactLevelOrderSupplierExact f B selected) high emits

end LogicLineages.PermittedControl.StageCallbackLevelOrder
