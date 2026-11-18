import LogicLineages.PersistentMarking.HereditaryDomainTargets
namespace LogicLineages.PersistentMarking.MarkedExtras
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode

abbrev Tagged := Ty × Code

def «universe» (E : Environment) (Γ : Context) : List Tagged :=
  dedupBy (fun a b => decide (a=b))
    (E.types.flatMap (fun σ => ((descriptor E σ).carriers Γ).map (fun c => (σ,c))))

def le (E : Environment) (Γ : Context) (a b : Tagged) : Bool :=
  decide (a.1=b.1) && (descriptor E a.1).le Γ a.2 b.2

def down (E : Environment) (Γ : Context) (xs : List Tagged) : List Tagged :=
  («universe» E Γ).filter (fun b => xs.any (fun a => le E Γ b a))

def DownClosed (E : Environment) (Γ : Context) (xs : List Tagged) : Prop :=
  ∀ a, a ∈ xs → ∀ b, b ∈ «universe» E Γ → le E Γ b a = true → b ∈ xs

def Canonical (E : Environment) (Γ : Context) (xs : List Tagged) : Prop :=
  xs = («universe» E Γ).filter (fun a => decide (a ∈ xs))

def Extra (E : Environment) (Γ : Context) (xs : List Tagged) : Prop :=
  Canonical E Γ xs ∧ DownClosed E Γ xs

def subsets {α : Type} : List α → List (List α)
  | [] => [[]]
  | a::as => subsets as ++ (subsets as).map (a::·)

def closedBool (E : Environment) (Γ : Context) (xs : List Tagged) : Bool :=
  xs.all (fun a => («universe» E Γ).all (fun b => if le E Γ b a then decide (b ∈ xs) else true))

def extras (E : Environment) (Γ : Context) : List (List Tagged) :=
  (subsets («universe» E Γ)).filter (closedBool E Γ)

def restricted (E : Environment) (Γ Θ : Context) (a : Tagged) : Tagged :=
  (a.1,(descriptor E a.1).restrict Γ Θ a.2)

def weaken (E : Environment) (Γ Θ : Context) (xs : List Tagged) : List Tagged :=
  down E Θ (xs.map (restricted E Γ Θ))
end LogicLineages.PersistentMarking.MarkedExtras
