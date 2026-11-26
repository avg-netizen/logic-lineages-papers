import LogicLineages.PersistentMarking.NumberedWindowTupleTargets

namespace LogicLineages.PersistentMarking.NumberedWindowRealizationShapeProof
open Spine NumberedWindowSyntax NumberedWindowTupleTargets

def TermShape (q : Expr) (Q : NTerm) : Prop :=
  Q.type = q.type ∧ NumberedWindowDomain.support Q = DecisionInventory.auxiliarySupport q ∧
    NumberedWindowDomain.heads Q = DecisionInventory.heads q

def ArgsShape (args : Spine.Args) (As : NArgs) : Prop :=
  As.length = args.length ∧ NumberedWindowDomain.argsSupport As = DecisionInventory.auxiliaryArgs args ∧
    NumberedWindowDomain.argsHeads As = DecisionInventory.headsArgs args

theorem termShape {n : Nat} {q : Expr} {Q : NTerm} (h : Realizes n q Q) : TermShape q Q := by
  induction h using Realizes.rec
    (motive_2 := fun args As _ => ArgsShape args As) with
  | free => exact ⟨rfl,rfl,rfl⟩
  | bound => exact ⟨rfl,rfl,rfl⟩
  | lam _ ih =>
    rcases ih with ⟨hType,hSupport,hHead⟩
    exact ⟨by simp only [NTerm.type,Expr.type,hType],
      by simp only [NumberedWindowDomain.support,DecisionInventory.auxiliarySupport,hType,hSupport],
      hHead⟩
  | ordinary _ ih =>
    rcases ih with ⟨_,hSupport,hHead⟩
    exact ⟨rfl,by simp only [NumberedWindowDomain.support,DecisionInventory.auxiliarySupport,hSupport],
      by simp only [NumberedWindowDomain.heads,DecisionInventory.heads,hHead]⟩
  | marked _ _ _ ihb ihe =>
    rcases ihb with ⟨_,hbS,hbH⟩
    rcases ihe with ⟨_,heS,heH⟩
    exact ⟨rfl,by simp only [NumberedWindowDomain.support,DecisionInventory.auxiliarySupport,hbS,heS],
      by simp only [NumberedWindowDomain.heads,DecisionInventory.heads,hbH,heH]⟩
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons _ _ ih iht =>
    rcases ih with ⟨_,hSupport,hHead⟩
    rcases iht with ⟨hl,htS,htH⟩
    exact ⟨by simp only [NArgs.length,Spine.Args.length,hl],
      by simp only [NumberedWindowDomain.argsSupport,DecisionInventory.auxiliaryArgs,hSupport,htS],
      by simp only [NumberedWindowDomain.argsHeads,DecisionInventory.headsArgs,hHead,htH]⟩

theorem argsShape {n : Nat} {args : Spine.Args} {As : NArgs}
    (h : RealizesArgs n args As) : ArgsShape args As := by
  cases h with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons h ht =>
    rcases termShape h with ⟨_,hSupport,hHead⟩
    rcases argsShape ht with ⟨hl,htS,htH⟩
    exact ⟨by simp only [NArgs.length,Spine.Args.length,hl],
      by simp only [NumberedWindowDomain.argsSupport,DecisionInventory.auxiliaryArgs,hSupport,htS],
      by simp only [NumberedWindowDomain.argsHeads,DecisionInventory.headsArgs,hHead,htH]⟩
termination_by sizeOf args

theorem weakensTerm {n m : Nat} {q : Expr} {Q : NTerm} (hm : m ≤ n)
    (h : Realizes n q Q) : Realizes m q Q := by
  induction h using Realizes.rec
    (motive_2 := fun args As _ => RealizesArgs m args As) with
  | free => exact .free
  | bound => exact .bound
  | lam _ ih => exact .lam ih
  | ordinary _ ih => exact .ordinary ih
  | marked hk _ _ ihb ihe => exact .marked (Nat.le_trans hm hk) ihb ihe
  | nil => exact .nil
  | cons _ _ ih iht => exact .cons ih iht

theorem weakensArgs {n m : Nat} {args : Spine.Args} {As : NArgs} (hm : m ≤ n)
    (h : RealizesArgs n args As) : RealizesArgs m args As := by
  cases h with
  | nil => exact .nil
  | cons h ht => exact .cons (weakensTerm hm h) (weakensArgs hm ht)
termination_by sizeOf args

theorem shiftTerm {n : Nat} {q : Expr} {Q : NTerm} (h : Realizes n q Q) :
    ∀ amount cutoff, Realizes n (Spine.shift amount cutoff q) (NumberedWindowSyntax.shift amount cutoff Q) := by
  induction h using Realizes.rec
    (motive_2 := fun args As _ => ∀ amount cutoff,
      RealizesArgs n (Spine.shiftArgs amount cutoff args) (NumberedWindowSyntax.shiftArgs amount cutoff As)) with
  | free => intros; exact .free
  | bound => intros; exact .bound
  | lam _ ih => intro amount cutoff; exact .lam (ih amount (cutoff+1))
  | ordinary _ ih => intro amount cutoff; exact .ordinary (ih amount cutoff)
  | marked hk _ _ ihb ihe => intro amount cutoff; exact .marked hk (ihb amount cutoff) (ihe amount cutoff)
  | nil => intros; exact .nil
  | cons _ _ ih iht => rename_i amount cutoff; exact .cons (ih amount cutoff) (iht amount cutoff)

theorem shiftArgs {n : Nat} {args : Spine.Args} {As : NArgs} (h : RealizesArgs n args As)
    (amount cutoff : Nat) :
    RealizesArgs n (Spine.shiftArgs amount cutoff args) (NumberedWindowSyntax.shiftArgs amount cutoff As) := by
  cases h with
  | nil => exact .nil
  | cons h ht => exact .cons (shiftTerm h amount cutoff) (shiftArgs ht amount cutoff)
termination_by sizeOf args

end LogicLineages.PersistentMarking.NumberedWindowRealizationShapeProof
