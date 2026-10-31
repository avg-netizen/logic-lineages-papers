module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealContextDefinitions
public import LogicLineages.ModelsAlgebra.Forests.RankedGraphImageDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealConstructors
open RankedParse RankedIdealContext

def downward (L : Term → Prop) (s : Term) : Prop :=
  ∃ t, L t ∧ Homeomorphic s t

def product (o : Operation) (I J : Term → Prop) : Term → Prop :=
  downward (fun t => ∃ l r, I l ∧ J r ∧ t = .node o l r)

/-- Actual finite iteration of independently chosen literal one-hole contexts. -/
inductive Star (K : Context → Prop) (B : Term → Prop) : Term → Prop where
  | base {t} : B t → Star K B t
  | step {c t} : K c → Star K B t → Star K B (plug c t)

def linearPiece (K : Context → Prop) (B : Term → Prop) : Term → Prop :=
  downward (Star K B)
end LogicLineages.ModelsAlgebra.Forests.RankedIdealConstructors
