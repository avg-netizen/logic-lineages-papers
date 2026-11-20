import LogicLineages.PersistentMarking.NumberedWindowConstructorOrderTargets
import LogicLineages.PersistentMarking.NumberedWindowExternalMultisetUnionProof

namespace LogicLineages.PersistentMarking.NumberedWindowConstructorOrderProof
open Spine NumberedWindowConstructorOrderTargets NumberedWindowArithmeticDirectMultisetTargets
open NumberedWindowExternalIDOperators NumberedWindowArithmeticFields
open NumberedWindowExternalMultisetUnionProof (coded_iff)

private abbrev J (S : Signature) (K : List Ty) (xs : List Nat) := Least (multisetStep S K) (encodeFields xs)
private abbrev Desc (S : Signature) (K : List Ty) (ys xs : List Nat) := AddressDirect S K xs ys
private abbrev Accessible (S : Signature) (K : List Ty) (m : Measure) := Acc (AdmittedEarlier S K) m

private theorem labelAccessible (l : Option Nat) : Acc LabelBelow l := by
  have fin (n : Nat) : Acc LabelBelow (some n) := by
    induction n using Nat.strongRecOn with
    | ind n ih =>
      constructor
      intro m e
      cases m with
      | none => exact False.elim e
      | some k => exact ih k e
  cases l with
  | some n => exact fin n
  | none =>
    constructor
    intro m e
    cases m with
    | none => exact False.elim e
    | some k => exact fin k

private theorem sourcePerm {S K xs ys zs} (p : xs.Perm ys) (h : AddressDirect S K xs zs) :
    AddressDirect S K ys zs :=
  (NumberedWindowArithmeticDirectMultisetDomain.permutations S K xs ys zs zs p (List.Perm.refl zs)).mp h

private def ByRank (S : Signature) (K : List Ty) (n : Nat) : Prop :=
  ∀ m : Measure, classRank S m.head = some n → J S K m.base → J S K m.extras → Accessible S K m

private def ByBase (S : Signature) (K : List Ty) (n : Nat) (base : List Nat) : Prop :=
  ∀ m : Measure, classRank S m.head = some n → m.base.Perm base → J S K m.extras → Accessible S K m

private def ByLabel (S : Signature) (K : List Ty) (n : Nat) (base : List Nat) (l : Option Nat) : Prop :=
  ∀ m : Measure, classRank S m.head = some n → m.base.Perm base → m.label = l →
    J S K m.extras → Accessible S K m

private def ByExtra (S : Signature) (K : List Ty) (n : Nat) (base : List Nat) (l : Option Nat)
    (es : List Nat) : Prop :=
  ∀ m : Measure, classRank S m.head = some n → m.base.Perm base → m.label = l →
    m.extras.Perm es → Accessible S K m

private theorem extraInduction {S K n base l}
    (heads : ∀ smaller, smaller < n → ByRank S K smaller)
    (bases : ∀ b, AddressDirect S K base b → ByBase S K n b)
    (labels : ∀ k, LabelBelow k l → ByLabel S K n base k)
    (es : List Nat) (he : Acc (Desc S K) es) : ByExtra S K n base l es := by
  induction he with
  | intro es _ extras =>
    intro m rank bm lm em
    constructor
    intro t h
    obtain ⟨domain,earlier⟩ := h
    rcases earlier with decreased | ⟨same,rest⟩
    · obtain ⟨r,s,hr,hs,lt⟩ := decreased
      have eq := Option.some.inj (hr.symm.trans rank)
      exact heads s (eq ▸ lt) t hs domain.2.1 domain.2.2
    · obtain ⟨r,hr,ht⟩ := same
      have tr : classRank S t.head = some n := ht.trans (hr.symm.trans rank)
      rcases rest with baseStep | ⟨sameBase,late⟩
      · exact bases t.base (sourcePerm bm baseStep) t tr (List.Perm.refl _) domain.2.2
      · have tb : t.base.Perm base := sameBase.symm.trans bm
        rcases late with labelStep | ⟨sameLabel,extraStep⟩
        · exact labels t.label (lm ▸ labelStep) t tr tb rfl domain.2.2
        · exact extras t.extras (sourcePerm em extraStep) t tr tb (sameLabel.symm.trans lm) (List.Perm.refl _)

private theorem labelsFrom {S K n base}
    (heads : ∀ smaller, smaller < n → ByRank S K smaller)
    (bases : ∀ b, AddressDirect S K base b → ByBase S K n b)
    (label : Option Nat) (h : Acc LabelBelow label) : ByLabel S K n base label := by
  induction h with
  | intro l _ labels =>
    intro m rank bm lm es
    exact extraInduction heads bases labels m.extras ((coded_iff S K m.extras).mp es).2
      m rank bm lm (List.Perm.refl _)

private theorem basesFrom {S K n} (heads : ∀ smaller, smaller < n → ByRank S K smaller)
    (base : List Nat) (h : Acc (Desc S K) base) : ByBase S K n base := by
  induction h with
  | intro b _ bases =>
    intro m rank bm es
    exact labelsFrom heads bases m.label (labelAccessible m.label) m rank bm rfl es

private theorem ranks (S : Signature) (K : List Ty) (n : Nat) : ByRank S K n := by
  induction n using Nat.strongRecOn with
  | ind n heads =>
    intro m rank bs es
    exact basesFrom heads m.base ((coded_iff S K m.base).mp bs).2 m rank (List.Perm.refl _) es

theorem accessible : ConstructorMeasureAccessible := by
  intro S K m domain
  obtain ⟨r,hr⟩ := domain.1.1
  exact ranks S K r m hr domain.2.1 domain.2.2

theorem inductionPrinciple : ConstructorMeasureInduction := by
  intro S K P step m domain
  have allAcc := accessible S K m domain
  revert domain
  induction allAcc with
  | intro m _ ih =>
    intro dom
    exact step m dom (fun t ht earlier => ih t ⟨ht,earlier⟩ ht)

end LogicLineages.PersistentMarking.NumberedWindowConstructorOrderProof
