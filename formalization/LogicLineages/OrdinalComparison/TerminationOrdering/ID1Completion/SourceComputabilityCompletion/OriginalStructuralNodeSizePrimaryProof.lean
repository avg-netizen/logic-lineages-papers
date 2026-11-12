module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizePrimaryTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizePrimaryProof
open Source NumberedRewriteSyntax NumberedPrimaryEquivalence NumberedAuxiliaryCoding OriginalStructuralNodeSize
open NumberedRewriteReduction

def weight {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} : List (Packed Symbol arity Gamma) → Nat
  | [] => 1
  | q :: rest => 1 + nodeCount (termCode q.2) + weight rest

theorem weightPerm {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    {qs rs : List (Packed Symbol arity Gamma)} (h : qs.Perm rs) : weight qs = weight rs := by
  induction h with
  | nil => rfl
  | cons q h ih => exact congrArg (1 + nodeCount (termCode q.2) + ·) ih
  | swap q r rest => simp only [weight]; omega
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem argumentWeight {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty}
    (args : AuxArguments Symbol arity Gamma types) : weight (argumentList args) = nodeCount (argumentsCode args) := by
  induction types with
  | nil => cases args; rfl
  | cons sigma types ih => cases args with
    | cons q rest => exact congrArg (1 + nodeCount (termCode q) + ·) (ih rest)

theorem permutationNodes {Symbol : Type} {arity : Symbol → Nat} {Gamma xs ys : List Ty}
    (a : AuxArguments Symbol arity Gamma xs) (b : AuxArguments Symbol arity Gamma ys)
    (h : (argumentList a).Perm (argumentList b)) : nodeCount (argumentsCode a) = nodeCount (argumentsCode b) := by
  rw [← argumentWeight a, ← argumentWeight b]
  exact weightPerm h

theorem actualPrimaryInvariant : OriginalStructuralNodeSizePrimaryTargets.PrimaryInvariant := by
  intro Symbol arity Gamma q r h
  induction h using Primary.rec
    (motive_2 := fun Gamma types base target _ => nodeCount (argumentsCode base) = nodeCount (argumentsCode target))
  case refl => rfl
  case symm h ih => exact ih.symm
  case trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  case ordinary f g base target he ht hp => exact congrArg (1+·) (permutationNodes base target hp)
  case numbered k f g tau base target types extras he hp =>
    exact congrArg (fun n => 1+n+nodeCount (argumentsCode extras)) (permutationNodes base target hp)
  case lam q r h ih => exact congrArg (1+·) ih
  case appFunction q r a h ih => exact congrArg (fun n => 1+n+nodeCount (termCode a)) ih
  case appArgument q a b h ih => exact congrArg (1+nodeCount (termCode q)+·) ih
  case ordinaryArguments f base target h ih => exact congrArg (1+·) ih
  case numberedBase k f tau base target types extras h ih =>
    exact congrArg (fun n => 1+n+nodeCount (argumentsCode extras)) ih
  case numberedExtras k f tau base types extras target h ih =>
    exact congrArg (1+nodeCount (argumentsCode base)+·) ih
  case nil => rfl
  case cons q r rest target hq hr ihq ihr => exact congrArg₂ (fun a b => 1+a+b) ihq ihr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizePrimaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizePrimaryProof
