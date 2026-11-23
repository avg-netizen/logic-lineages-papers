module

public import LogicLineages.NativeModule.PersistentMarking.DecisionObservations

@[expose] public section

namespace LogicLineages.PersistentMarking.FiniteDomainFoundation
open Spine NameBridge DecisionPorts

mutual
 def exprEq : Expr → Expr → Bool
  | .free σ x,.free τ y => decide (σ=τ) && decide (x=y)
  | .bound σ i,.bound τ j => decide (σ=τ) && decide (i=j)
  | .lam σ q,.lam τ r => decide (σ=τ) && exprEq q r
  | .head f qs,.head g rs => decide (f=g) && argsEq qs rs
  | .marked f σ qs es,.marked g τ rs fs =>
      decide (f=g) && decide (σ=τ) && argsEq qs rs && argsEq es fs
  | _,_ => false
 def argsEq : Args → Args → Bool
  | .nil,.nil => true
  | .cons q qs,.cons r rs => exprEq q r && argsEq qs rs
  | _,_ => false
end

def dedupBy (same : α → α → Bool) : List α → List α
  | [] => []
  | x::xs => if xs.any (same x) then dedupBy same xs else x::dedupBy same xs

def distinctObservations (xs : List Expr) : List Expr := dedupBy exprEq xs
def distinctContexts (xs : List Context) : List Context := dedupBy (fun Γ Δ => decide (Γ=Δ)) xs

def typeSize : Ty → Nat
  | .ground => 1
  | .arrow σ τ => 1 + typeSize σ + typeSize τ

/- Every nonempty prefix, including function-valued residuals. -/
def fullPrefixes : Ty → List (List Ty × Ty)
  | .ground => []
  | .arrow σ τ => ([σ],τ) :: (fullPrefixes τ).map (fun p => (σ::p.1,p.2))

/- Raw finite coordinate enumeration, not a semantic domain or a source-size
cutoff. Zero bounds and the empty schema have their literal meanings. -/
def vectors : List Nat → List (List Nat)
  | [] => [[]]
  | n::ns => (List.range n).flatMap (fun i => (vectors ns).map (i::·))

def Fits : List Nat → List Nat → Prop
  | [],[] => True
  | n::ns,i::is => i<n ∧ Fits ns is
  | _,_ => False
end LogicLineages.PersistentMarking.FiniteDomainFoundation
