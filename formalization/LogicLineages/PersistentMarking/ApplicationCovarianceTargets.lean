import LogicLineages.PersistentMarking.ExtendedComparison
import LogicLineages.PersistentMarking.UnaryCallSyntax
namespace LogicLineages.PersistentMarking.ApplicationCovarianceTargets
open Spine

/-- One-way plugging of an older bound-value block into an actually successful
original auxiliary call. Arbitrary values, not only free variables/prefix copies. -/
def SuccessfulAuxPlugging : Prop := ∀ q newer older args w,
  applyAux q args (newer.append older) = some w →
  applyAux (substitute older newer.length q) args newer = some w

/-- Original full success implies the same sequential unary result, never the converse. -/
def SuccessfulUnaryStages : Prop := ∀ q args r, apply q args = some r → unaryCalls q args = some r

def SourceSuccess : Prop := ∀ S q s as bs τ r,
  ExtendedWeak S q s → _root_.Nonempty (ExtendedOrderedTree S as bs) →
  CallTyped EmptyContext q.type as τ → CallTyped EmptyContext s.type bs τ →
  apply s bs = some r → ∃ p, apply q as = some p

def UnaryTransport : Prop := ∀ S q s a b τ r,
  ExtendedWeak S q s → ExtendedWeak S a b →
  CallTyped EmptyContext q.type (.cons a .nil) τ → CallTyped EmptyContext s.type (.cons b .nil) τ →
  apply s (.cons b .nil) = some r → ∃ p, apply q (.cons a .nil) = some p ∧ ExtendedWeak S p r

/-- Complete printed application covariance for the actual original full calls. -/
def FullApplication : Prop := ∀ S q s as bs τ r,
  ExtendedWeak S q s → _root_.Nonempty (ExtendedOrderedTree S as bs) →
  CallTyped EmptyContext q.type as τ → CallTyped EmptyContext s.type bs τ →
  apply s bs = some r → ∃ p, apply q as = some p ∧ ExtendedWeak S p r
end LogicLineages.PersistentMarking.ApplicationCovarianceTargets
