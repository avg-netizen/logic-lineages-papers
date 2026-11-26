import LogicLineages.PersistentMarking.NumberedWindowSyntax
import LogicLineages.PersistentMarking.DecisionSourceUniverse

namespace LogicLineages.PersistentMarking.NumberedWindowDomain
open Spine NumberedWindowSyntax
open TypeSupport (subtypes)
open DecisionInventory (declaration)

mutual
inductive Typed : BoundContext → NTerm → Ty → Prop where
  | free : Typed C (.free σ x) σ
  | bound : C i = some σ → Typed C (.bound σ i) σ
  | lam : Typed (C.push σ) body τ → Typed C (.lam σ body) (.arrow σ τ)
  | bottom : Typed C (.bottom τ) τ
  | ordinary : BaseTyped C bs f.arguments → Typed C (.ordinary f bs) f.result
  | numbered : BaseTyped C bs f.arguments → ExtrasTyped C es → Typed C (.numbered f τ k bs es) τ
  | auxApp : Typed C q (.arrow σ τ) → Typed C a σ → Typed C (.auxApp σ τ q a) τ
inductive BaseTyped : BoundContext → NArgs → List Ty → Prop where
  | nil : BaseTyped C .nil []
  | cons : Typed C a τ → BaseTyped C rest types → BaseTyped C (.cons a rest) (τ :: types)
inductive ExtrasTyped : BoundContext → NArgs → Prop where
  | nil : ExtrasTyped C .nil
  | cons : Typed C a τ → ExtrasTyped C rest → ExtrasTyped C (.cons a rest)
end

mutual
def support : NTerm → List Ty
  | .free σ _ | .bound σ _ | .bottom σ => subtypes σ
  | .lam σ body => subtypes (.arrow σ body.type) ++ subtypes σ ++ support body
  | .ordinary f bs => declaration f ++ argsSupport bs
  | .numbered f τ _ bs es => declaration f ++ subtypes τ ++ argsSupport bs ++ argsSupport es
  | .auxApp σ τ q a => subtypes τ ++ subtypes σ ++ support q ++ support a
def argsSupport : NArgs → List Ty
  | .nil => []
  | .cons a rest => support a ++ argsSupport rest
end

mutual
def heads : NTerm → List Head
  | .free _ _ | .bound _ _ | .bottom _ => []
  | .lam _ body => heads body
  | .ordinary f bs => f :: argsHeads bs
  | .numbered f _ _ bs es => f :: (argsHeads bs ++ argsHeads es)
  | .auxApp _ _ q a => heads q ++ heads a
def argsHeads : NArgs → List Head
  | .nil => []
  | .cons a rest => heads a ++ argsHeads rest
end

def HeadInWindow (S : Signature) (K : List Ty) (f : Head) : Prop :=
  Admitted S f ∧ ∀ τ, τ ∈ declaration f → τ ∈ K

def InWindow (S : Signature) (K : List Ty) (C : BoundContext) (τ : Ty) (q : NTerm) : Prop :=
  Typed C q τ ∧ (∀ σ, σ ∈ support q → σ ∈ K) ∧
    (∀ f, f ∈ heads q → HeadInWindow S K f)

/-- Declaration-retaining symbolic admissibility, not the decision
procedure's designated source-head, target-subterm or finite-port guard. -/
def SymbolicAdmissible (K : List Ty) (q : Expr) : Prop :=
  ∀ σ, σ ∈ DecisionInventory.auxiliarySupport q → σ ∈ K

def SymbolicArgsAdmissible (K : List Ty) (args : Spine.Args) : Prop :=
  ∀ σ, σ ∈ DecisionInventory.auxiliaryArgs args → σ ∈ K

end LogicLineages.PersistentMarking.NumberedWindowDomain
