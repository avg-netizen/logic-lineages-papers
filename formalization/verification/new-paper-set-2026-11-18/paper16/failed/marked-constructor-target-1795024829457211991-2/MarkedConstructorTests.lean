import LogicLineages.PersistentMarking.ProtectedSpineEnvironment
namespace LogicLineages.PersistentMarking.MarkedConstructorTests
open Spine NameBridge DecisionPorts FiniteDomainFoundation HereditaryDomainCode HereditaryDomainSemantics
open MarkedFamilyParameters (Parameter)

def terms : Args → List Expr
  | .nil => []
  | .cons q qs => q :: terms qs

def removals : List Expr → List (Expr × List Expr)
  | [] => []
  | q::qs => (q,qs) :: (removals qs).map (fun p => (p.1,q::p.2))

def splits {α : Type} : List α → List (List α × List α)
  | [] => [([],[])]
  | x::xs => (splits xs).flatMap fun p => [(x::p.1,p.2),(p.1,x::p.2)]

def bit (strict : Bool) (E : Environment) (Γ : Context) (a : MarkedExtras.Tagged) (t : Expr) : Bool :=
  decide (a.1=t.type) &&
    (if strict then (HereditaryDomainSemantics.decode E a.1 Γ a.2).strict Γ t
     else (HereditaryDomainSemantics.decode E a.1 Γ a.2).weak Γ t)

def matching (E : Environment) (Γ : Context) : List MarkedExtras.Tagged → List Expr → Bool
  | [], ts => ts.isEmpty
  | a::bs, ts => (removals ts).any fun p => bit false E Γ a p.1 && matching E Γ bs p.2

def coverage (E : Environment) (Γ : Context) (removed : List MarkedExtras.Tagged) (added : List Expr) : Bool :=
  added.all fun t => removed.any fun a => bit true E Γ a t

def multiset (E : Environment) (Γ : Context) (bs : List MarkedExtras.Tagged) (ts : List Expr) : Bool :=
  (splits bs).any fun source => !source.2.isEmpty &&
    (splits ts).any fun target => matching E Γ source.1 target.1 && coverage E Γ source.2 target.2

def owner (E : Environment) (heads : List Head) (M : Code) (p : Parameter) (τ : Ty) : Option Code :=
  StructuralActions.markedAction E heads M (p.1,τ,p.2.2.1,p.2.2.2.1,p.2.2.2.2)

def ownerTuple (E : Environment) (heads : List Head) (M : Code) (p : Parameter) (ds : List Ty) : Option (List Code) :=
  ds.mapM (owner E heads M p)

def whole (E : Environment) (heads : List Head) (M : Code) (p : Parameter) (ts : List Expr) : Bool :=
  ts.all fun t => match owner E heads M p t.type with
    | none => false
    | some c => (HereditaryDomainSemantics.decode E t.type p.2.2.1 c).weak p.2.2.1 t

def selected (E : Environment) (heads : List Head) (M : Code) (p : Parameter)
    (a : MarkedExtras.Tagged) (ds : List Ty) (t : Expr) : Bool :=
  match ds with
  | [] => bit false E p.2.2.1 a t
  | _::_ => match ownerTuple E heads M p ds with
    | none => false
    | some xs =>
      let c := StructuralActions.fullAction E a.1 p.2.2.1 a.2 ds p.2.1 xs
      (HereditaryDomainSemantics.decode E p.2.1 p.2.2.1 c).weak p.2.2.1 t

def selectTest (E : Environment) (heads : List Head) (M : Code) (p : Parameter) (t : Expr) : Bool :=
  (p.1.arguments.zip p.2.2.2.1 ++ p.2.2.2.2).any fun a =>
    (([],a.1)::fullPrefixes a.1).any fun suffix =>
      decide (suffix.2=p.2.1) && selected E heads M p a suffix.1 t

def equivalent (S : Signature) (f g : Head) : Bool :=
  match classRank S f,classRank S g with
  | some a,some b => decide (a=b)
  | _,_ => false

def precedes (S : Signature) (f g : Head) : Bool :=
  match classRank S f,classRank S g with
  | some a,some b => decide (b<a)
  | _,_ => false

def copyTest (S : Signature) (E : Environment) (heads : List Head) (M : Code) (p : Parameter) (t : Expr) : Bool :=
  match t with
  | .head g ts => decide (g.result=p.2.1) && precedes S p.1 g && whole E heads M p (terms ts)
  | _ => false

def statTest (S : Signature) (E : Environment) (heads : List Head) (M : Code) (p : Parameter) (t : Expr) : Bool :=
  match t with
  | .head g ts => decide (g.result=p.2.1) && equivalent S p.1 g &&
      multiset E p.2.2.1 (p.1.arguments.zip p.2.2.2.1) (terms ts) && whole E heads M p (terms ts)
  | _ => false

def fabsParameter (E : Environment) (p : Parameter) (σ τ : Ty) (i : Nat) : Parameter :=
  let Θ := ProtectedSpineEnvironment.openingContext p.2.2.1 σ i
  let w := MarkedFamilyCoherence.weakenParameter E p Θ
  let v := ProtectedSpineEnvironment.literalCode E Θ σ (portName E.names i)
  (p.1,τ,Θ,w.2.2.2.1,StructuralActions.insertExtras E Θ w.2.2.2.2 [(σ,v)])

def fabsTest (E : Environment) (heads : List Head) (M : Code) (p : Parameter) (t : Expr) : Bool :=
  match p.2.1,t with
  | .arrow σ τ,.lam ρ body =>
    if σ=ρ then match ProtectedSpineEnvironment.openingSlot p.2.2.1 with
      | none => false
      | some i =>
        let q := fabsParameter E p σ τ i
        match StructuralActions.markedAction E heads M q with
        | none => false
        | some c => (HereditaryDomainSemantics.decode E τ q.2.2.1 c).weak q.2.2.1
            (openBody σ (portName E.names i) body)
    else false
  | _,_ => false

def weakTest (S : Signature) (E : Environment) (heads : List Head) (M : Code) (p : Parameter) (t : Expr) : Bool :=
  selectTest E heads M p t || copyTest S E heads M p t || statTest S E heads M p t || fabsTest E heads M p t
end LogicLineages.PersistentMarking.MarkedConstructorTests
