module
public import LogicLineages.OrdinalComparison.SourceOneUnitDefinitions
public import LogicLineages.OrdinalComparison.SourceAbsoluteObserverDefinitions
public import LogicLineages.OrdinalComparison.WWUnitObservationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitElimination
open OriginalDomain

/-- One shared natural component valuation: ground inputs are encoded naturals;
functional unit coordinates have encoding zero. -/
def inputs {Γ} (ρ : Variable Γ .ground → Nat) : OrdinalComponent Γ → Nat
  | ⟨.ground,x,_⟩ => ρ x
  | ⟨.arrow _ _,_,_⟩ => 0

/-- The only source atoms in a ground block are actual ground-output sources
with the original remaining ground names and two fresh ground witnesses. -/
structure GroundBlock (α : Type) (Γ : List Ty) where
  allGround : ∀ σ ∈ Γ, σ=Ty.ground
  left : OriginalTerm (.ground::.ground::Γ) .ground
  right : OriginalTerm (.ground::.ground::Γ) .ground
  factor : Nat
  anchor : α

/-- Finite existential/conjunctive linear syntax. Internal nodes introduce
scalar witnesses, not arbitrary semantic graph predicates. Every source atom
is stored literally in a GroundBlock. -/
inductive Tree (α : Type) : List Ty → Type where
  | leaf {Γ} : GroundBlock α Γ → Tree α Γ
  | free (left right : List Ty) (σ : Ty) (d : Nat) :
      Tree α (left++right) → Tree α (left++σ::right)
  | active (left right : List Ty) (σ : Ty) (p d d' c : Nat) :
      Tree α (left++right) → Tree α (left++right) → Tree α (left++σ::right)

def mapAnchors {α β : Type} (f : α → β) {Γ} : Tree α Γ → Tree β Γ
  | .leaf b => .leaf ⟨b.allGround,b.left,b.right,b.factor,f b.anchor⟩
  | .free left right σ d q => .free left right σ d (mapAnchors f q)
  | .active left right σ p d d' c q r =>
      .active left right σ p d d' c (mapAnchors f q) (mapAnchors f r)

def anchors {α : Type} {Γ} : Tree α Γ → List α
  | .leaf b => [b.anchor]
  | .free _ _ _ _ q => anchors q
  | .active _ _ _ _ _ _ _ q r => anchors q++anchors r

abbrev LeafSource := Σ Γ : List Ty, OriginalTerm Γ .ground

def sources {α : Type} {Γ} : Tree α Γ → List LeafSource
  | .leaf (Γ := Δ) b => [⟨.ground::.ground::Δ,b.left⟩,⟨.ground::.ground::Δ,b.right⟩]
  | .free _ _ _ _ q => sources q
  | .active _ _ _ _ _ _ _ q r => sources q++sources r

noncomputable def programValues (xs : List (Nat×Nat)) : List Nat := xs.map AbsoluteObserver.openSourceValue

noncomputable def realize {Γ} (q : Tree (Nat×Nat) Γ) : Tree Nat Γ :=
  mapAnchors AbsoluteObserver.openSourceValue q

/-- Only ordinary natural constants occur after realization. Ground source
observations have their exact +1 encoding; no functional source is observed
as an unexplained leaf. -/
noncomputable def Eval {Γ} : Tree Nat Γ → (Variable Γ .ground → Nat) → Nat → Prop
  | .leaf b, ρ, r => ∃ x y q : Nat,
      AbsoluteObserver.Observation (AbsoluteObserver.extend (inputs ρ) x y) b.left q ∧
      AbsoluteObserver.Observation (AbsoluteObserver.extend (inputs ρ) x y) b.right q ∧
      b.factor*r+(x+1)=b.factor*b.anchor+(y+1)
  | .free left right σ d q, ρ, r => ∃ l : Nat,
      Eval q (UnitObservation.remainingInputs left right σ ρ) (l+1) ∧ l+1=(d+1)*r+d
  | .active left right σ p d d' c q s, ρ, r => ∃ l l' : Nat,
      Eval q (UnitObservation.remainingInputs left right σ ρ) (l+1) ∧
      Eval s (UnitObservation.remainingInputs left right σ ρ) (l'+1) ∧
      p*d'*(l+1)+d*c=d*(l'+1)+p*(d'-d)*r

inductive Selection : List Ty → Type where
  | ground {Γ} : (∀ σ ∈ Γ, σ=Ty.ground) → Selection Γ
  | found (left right : List Ty) (σ : Ty) : 0<σ.level → Selection (left++σ::right)

def select : (Γ : List Ty) → Selection Γ
  | [] => .ground (by simp)
  | .ground::Γ => match select Γ with
    | .ground h => .ground (by intro σ hσ; rcases List.mem_cons.mp hσ with rfl | hσ; rfl; exact h σ hσ)
    | .found left right σ hσ => .found (.ground::left) right σ hσ
  | .arrow a b::Γ => .found [] Γ (.arrow a b) (by simp only [Ty.level]; omega)

def groundBlock {Γ τ} (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) (t : OriginalTerm Γ τ) : GroundBlock (Nat×Nat) Γ :=
  ⟨hΓ,AbsoluteObserver.originalProbe t,AbsoluteObserver.closedProbe hΓ t,
    AbsoluteObserver.factor τ,(Γ.length,SyntaxCode.encodeTerm t)⟩

/-- One structural compilation step, with a polymorphic recursive call. -/
def step (rec : {Γ : List Ty} → {τ : Ty} → OriginalTerm Γ τ → Option (Tree (Nat×Nat) Γ)) :
    {Γ : List Ty} → {τ : Ty} → Selection Γ → OriginalTerm Γ τ → Option (Tree (Nat×Nat) Γ)
  | _,_,.ground hΓ,t => some (.leaf (groundBlock hΓ t))
  | _,τ,.found left right σ hσ,t => do
      let a := t.rename (SelectedBinder.moveToHead left right σ)
      let d ← OneUnit.compile a
      if d.free then
        let q ← rec (OneUnit.first a)
        pure (.free left right σ d.d q)
      else
        let q ← rec (OneUnit.first a)
        let r ← rec (OneUnit.second a)
        pure (.active left right σ (OneUnit.coefficient τ) d.d d.d' (OneUnit.constant τ d) q r)

/-- Executable symbolic compiler. Its only failures are exhausted structural
fuel or a refusing actual source assignment; totality is a theorem, not a
premise. No ordinal value is evaluated during this finite syntax recursion. -/
def build : (fuel : Nat) → {Γ : List Ty} → {τ : Ty} → OriginalTerm Γ τ → Option (Tree (Nat×Nat) Γ)
  | 0,_,_,_ => none
  | fuel+1,Γ,_,t => step (fun {_ _} a => build fuel a) (select Γ) t
end LogicLineages.OrdinalComparison.Source.UnitElimination
