import LogicLineages.PersistentMarking.NumberedWindowRules

namespace LogicLineages.PersistentMarking.NumberedWindowTupleTargets
open Spine NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules

/- The actual realized shape has the original symbols, current output
annotations, list order and globally typed names. Each symbolic mark gets
its own finite label at or above the same threshold. Neither bottom nor
an auxiliary application realizes symbolic syntax. -/
mutual
inductive Realizes (n : Nat) : Expr → NTerm → Prop where
  | free : Realizes n (.free σ x) (.free σ x)
  | bound : Realizes n (.bound σ i) (.bound σ i)
  | lam : Realizes n q Q → Realizes n (.lam σ q) (.lam σ Q)
  | ordinary : RealizesArgs n bs Bs → Realizes n (.head f bs) (.ordinary f Bs)
  | marked : n ≤ k → RealizesArgs n bs Bs → RealizesArgs n es Es →
      Realizes n (.marked f τ bs es) (.numbered f τ k Bs Es)
inductive RealizesArgs (n : Nat) : Spine.Args → NArgs → Prop where
  | nil : RealizesArgs n .nil .nil
  | cons : Realizes n a A → RealizesArgs n tail Tail → RealizesArgs n (.cons a tail) (.cons A Tail)
end

/- These are supporting facts about the fixed numerical carrier. They
neither quantify all original comparison derivations nor cover the later
strict and weak numerical simulation's intermediates. -/
def RealizationInWindow : Prop := ∀ S K C σ n q Q,
  Spine.Typed C q σ → Valid S q → SymbolicAdmissible K q →
  Realizes n q Q → InWindow S K C σ Q

def RealizationWeakens : Prop := ∀ n m q Q, m ≤ n → Realizes n q Q → Realizes m q Q

def RealizationShift : Prop := ∀ n amount cutoff q Q,
  Realizes n q Q →
  Realizes n (Spine.shift amount cutoff q) (NumberedWindowSyntax.shift amount cutoff Q)

def RealizationSubstitution : Prop := ∀ n depth q Q values Values,
  Realizes n q Q → RealizesArgs n values Values →
  Realizes n (Spine.substitute values depth q) (NumberedWindowSyntax.substitute Values depth Q)

def budget (n : Nat) (args : Spine.Args) : Nat := n + args.length + 1

/-- Actual full-tuple simulation, with the literal defined original
simultaneous call and its actual result. No ordinary-head, closed-term or
fixed-point restriction: the binder stack is an arbitrary finite stack
and the free names remain globally typed. Retain the whole numerical
application spine and the exact +length+1 uniform threshold. -/
def WholeTupleSimulation : Prop := ∀ (S : Signature) (K : List Ty) (Γ : List Ty)
    (q r : Expr) (args : Spine.Args) (σ τ : Ty) (n : Nat) (Q : NTerm) (As : NArgs),
  let C := BoundContext.prefix Γ EmptyContext
  DecisionSourceUniverse.Closed K →
  Spine.Typed C q σ → Valid S q → CallTyped C σ args τ → ValidArgs S args →
  SymbolicAdmissible K q → SymbolicArgsAdmissible K args →
  Spine.apply q args = some r →
  Realizes (budget n args) q Q → RealizesArgs (budget n args) args As →
  ∃ start out, applications Q As = some start ∧
    WindowPath S K C τ start out ∧ Realizes n r out

end LogicLineages.PersistentMarking.NumberedWindowTupleTargets
