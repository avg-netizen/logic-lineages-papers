module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryEquivalenceTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryEquivalenceProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimaryEquivalence NumberedRewriteApplication

def weight {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} : List (Packed Symbol arity Gamma) → Nat
  | [] => 0
  | q::rest => size q.2+weight rest

theorem weightPerm {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    {qs rs : List (Packed Symbol arity Gamma)} (h : qs.Perm rs) : weight qs=weight rs := by
  induction h with
  | nil => rfl
  | cons q h ih => exact congrArg (size q.2+·) ih
  | swap q r rest => simp only [weight]; omega
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem argumentWeight {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty}
    (args : AuxArguments Symbol arity Gamma types) : weight (argumentList args)=argumentsSize args := by
  induction types with
  | nil => cases args; rfl
  | cons sigma types ih => cases args with
    | cons q rest => exact congrArg (size q+·) (ih rest)

theorem permutationSize {Symbol : Type} {arity : Symbol → Nat} {Gamma xs ys : List Ty}
    (a : AuxArguments Symbol arity Gamma xs) (b : AuxArguments Symbol arity Gamma ys)
    (h : (argumentList a).Perm (argumentList b)) : argumentsSize a=argumentsSize b := by
  rw [←argumentWeight a,←argumentWeight b]
  exact weightPerm h

theorem primaryTypePreservation : NumberedPrimaryEquivalenceTargets.ActualPrimaryTypePreservation := by
  intro Symbol arity Gamma q r h
  induction h using Primary.rec (motive_2 := fun _ _ _ _ _ => True)
  case refl => rfl
  case symm h ih => exact ih.symm
  case trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  case ordinary f g base target he ht hp => exact ht
  case numbered => rfl
  case lam => rfl
  case appFunction => rfl
  case appArgument => rfl
  case ordinaryArguments => rfl
  case numberedBase => rfl
  case numberedExtras => rfl
  case nil => trivial
  case cons => trivial

theorem primarySizePreservation : NumberedPrimaryEquivalenceTargets.ActualPrimarySizePreservation := by
  intro Symbol arity Gamma q r h
  induction h using Primary.rec
    (motive_2 := fun Gamma types base target _ => argumentsSize base=argumentsSize target)
  case refl => rfl
  case symm h ih => exact ih.symm
  case trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  case ordinary f g base target he ht hp => exact congrArg (1+·) (permutationSize base target hp)
  case numbered k f g tau base target types extras he hp =>
    exact congrArg (fun n => 1+n+argumentsSize extras) (permutationSize base target hp)
  case lam q r h ih => exact congrArg (1+·) ih
  case appFunction q r a h ih => exact congrArg (fun n => 1+n+size a) ih
  case appArgument q a b h ih => exact congrArg (1+size q+·) ih
  case ordinaryArguments f base target h ih => exact congrArg (1+·) ih
  case numberedBase k f tau base target types extras h ih =>
    exact congrArg (fun n => 1+n+argumentsSize extras) ih
  case numberedExtras k f tau base types extras target h ih =>
    exact congrArg (1+argumentsSize base+·) ih
  case nil => rfl
  case cons q r rest target hq hr ihq ihr => exact congrArg₂ (·+·) ihq ihr

theorem traceZeroOnly {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Gamma : List Ty} {n : Nat} {q r : Packed Symbol arity Gamma}
    (h : Trace Symbol arity above Gamma n q r) : n=0 → Primary Symbol arity Gamma q r := by
  induction h with
  | equivalent h => intro _; exact h
  | raw q r h => intro hn; omega
  | @trans m n q r s h₁ h₂ ih₁ ih₂ =>
    intro hmn
    have hm : m=0 := by omega
    have hn : n=0 := by omega
    exact .trans (ih₁ hm) (ih₂ hn)

theorem traceZero : NumberedPrimaryEquivalenceTargets.ActualTraceZero := by
  intro Symbol arity above Gamma q r
  constructor
  · intro h; exact traceZeroOnly h rfl
  · exact Trace.equivalent

theorem traceTypePreservation : NumberedPrimaryEquivalenceTargets.ActualTraceTypePreservation := by
  intro Symbol arity above Gamma n q r h
  induction h with
  | equivalent h => exact primaryTypePreservation Symbol arity _ _ _ h
  | raw q r h => rfl
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem rawPathTrace : NumberedPrimaryEquivalenceTargets.ActualRawPathTrace := by
  intro Symbol arity above Gamma tau q r h
  induction h with
  | refl q => exact ⟨0,.equivalent (.refl _)⟩
  | next q r s h hr ih =>
    obtain ⟨n,hn⟩ := ih
    exact ⟨1+n,.trans (.raw q r h) hn⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryEquivalenceProof
