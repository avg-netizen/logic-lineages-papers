import LogicLineages.PersistentMarking.NumberedWindowTupleTargets

namespace LogicLineages.PersistentMarking.NumberedWindowBindingTargets
open NumberedWindowSyntax

/-- Removal of one newly inserted binder preserves every original deeper
index, including under residual lambdas and in original base/extra lists. -/
def SingleCancellation : Prop := ∀ a k cutoff Q,
  substitute (.cons a .nil) (k + cutoff) (shift (k + 1) cutoff Q) = shift k cutoff Q

def SingleArgsCancellation : Prop := ∀ a k cutoff As,
  substituteArgs (.cons a .nil) (k + cutoff) (shiftArgs (k + 1) cutoff As) = shiftArgs k cutoff As

/-- One numerical beta step on the original partially consumed spine uses
the very same nearest-binder-first block as the literal symbolic call. -/
def SinglePushBlock : Prop := ∀ a values depth Q,
  substitute (.cons a .nil) depth (substitute values (depth + 1) Q) =
    substitute (.cons a values) depth Q

def SingleArgsPushBlock : Prop := ∀ a values depth As,
  substituteArgs (.cons a .nil) depth (substituteArgs values (depth + 1) As) =
    substituteArgs (.cons a values) depth As

/-- The actual abstraction-body beta result appends exactly the supplied
numerical argument; the original base, old extras and marked owner label
are otherwise unchanged. The raw rule still pays the leading decrement
separately before creating this abstraction. -/
def OpenNumberedBeta : Prop := ∀ f σ τ k bs es a,
  substitute (.cons a .nil) 0 (openNumbered f σ τ k bs es) =
    .numbered f τ k bs (es.append (.cons a .nil))

end LogicLineages.PersistentMarking.NumberedWindowBindingTargets
