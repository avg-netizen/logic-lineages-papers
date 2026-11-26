module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowBindingTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowApplicationTargets
open Spine NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules NumberedWindowTupleTargets

/-- In-order numeric arguments with the actual supplied domain at each
position. The single window/outer context and actual typed entries are
retained; no intermediate source ordering is assumed. -/
inductive ArgsWindow (S : Signature) (K : List Ty) (C : BoundContext) : List Ty → NArgs → Prop where
  | nil : ArgsWindow S K C [] .nil
  | cons : InWindow S K C σ a → ArgsWindow S K C ds As →
      ArgsWindow S K C (σ :: ds) (.cons a As)

def RealizedCallArgs : Prop := ∀ S K C σ τ args As n,
  CallTyped C σ args τ → ValidArgs S args → SymbolicArgsAdmissible K args →
  RealizesArgs n args As →
  ∃ ds, σ = ArrowPrefix ds τ ∧ ds.length = args.length ∧ ArgsWindow S K C ds As

def AppInWindow : Prop := ∀ S K C σ τ Q A,
  DecisionSourceUniverse.Closed K →
  InWindow S K C (.arrow σ τ) Q → InWindow S K C σ A →
  InWindow S K C τ (.auxApp σ τ Q A)

def ApplicationsInWindow : Prop := ∀ S K C ds τ Q As,
  DecisionSourceUniverse.Closed K →
  InWindow S K C (ArrowPrefix ds τ) Q → ArgsWindow S K C ds As →
  ∃ start, applications Q As = some start ∧ InWindow S K C τ start

def LiftAuxFunction : Prop := ∀ S K C σ τ Q R A,
  DecisionSourceUniverse.Closed K →
  WindowPath S K C (.arrow σ τ) Q R → InWindow S K C σ A →
  WindowPath S K C τ (.auxApp σ τ Q A) (.auxApp σ τ R A)

def LiftApplications : Prop := ∀ S K C ds τ Q R As,
  DecisionSourceUniverse.Closed K →
  WindowPath S K C (ArrowPrefix ds τ) Q R → ArgsWindow S K C ds As →
  ∃ start out, applications Q As = some start ∧ applications R As = some out ∧
    WindowPath S K C τ start out

def OpenNumberedInWindow : Prop := ∀ S K C f σ τ k bs es,
  DecisionSourceUniverse.Closed K →
  InWindow S K C (.arrow σ τ) (.numbered f (.arrow σ τ) (k+1) bs es) →
  InWindow S K C (.arrow σ τ) (.lam σ (openNumbered f σ τ k bs es))

def AppendArgumentInWindow : Prop := ∀ S K C f σ τ k bs es A,
  DecisionSourceUniverse.Closed K →
  InWindow S K C (.arrow σ τ) (.numbered f (.arrow σ τ) (k+1) bs es) →
  InWindow S K C σ A →
  InWindow S K C τ (.numbered f τ k bs (es.append (.cons A .nil)))

/-- Support only: the already-numbered functional branch, with one
actual finite decrement per numerical argument, is not the numbered
protected-spine whole-tuple theorem. -/
def WholeNumberedAppend : Prop := ∀ S K C ds τ f k bs es As,
  DecisionSourceUniverse.Closed K →
  InWindow S K C (ArrowPrefix ds τ) (.numbered f (ArrowPrefix ds τ) (k+ds.length) bs es) →
  ArgsWindow S K C ds As →
  ∃ start, applications (.numbered f (ArrowPrefix ds τ) (k+ds.length) bs es) As = some start ∧
    WindowPath S K C τ start (.numbered f τ k bs (es.append As))

end LogicLineages.PersistentMarking.NumberedWindowApplicationTargets
