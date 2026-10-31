module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRankDefinitions
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealConstructorsDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealSpine
open RankedParse ProfileAutomatonEncoding RankedIdealCompletion RankedIdealComponents RankedIdealRank RankedIdealContext
/-- Ground entries include every strict lower epsilon predecessor, not only
binary entries. All recursive side-state calls strictly decrease finite rank. -/
inductive Entry (M : Machine) [DecidableEq M.State] (q : M.State) : Term → Prop where
 | atom : SameComponent M q M.leaf → Entry M q .atom
 | lower {p t} : Lower M p q → Run M t p → Entry M q t
 | node {o x y l r} : Lower M x q → Lower M y q →
     SameComponent M q (M.node o x y) →
     x ∈ productive M → y ∈ productive M → Run M l x → Run M r y →
     Entry M q (.node o l r)
/-- Literal one-step contexts within a linear component. Their side state lies
strictly below the component; no directedness or decomposition is assumed. -/
inductive Frame (M : Machine) [DecidableEq M.State] (q : M.State) : Context → Prop where
 | left {o x y r} : SameComponent M q x → Lower M y q →
     SameComponent M q (M.node o x y) →
     x ∈ productive M → y ∈ productive M → Run M r y →
     Frame M q (.left o .hole r)
 | right {o x y l} : Lower M x q → SameComponent M q y →
     SameComponent M q (M.node o x y) →
     x ∈ productive M → y ∈ productive M → Run M l x →
     Frame M q (.right o l .hole)
end LogicLineages.ModelsAlgebra.Forests.RankedIdealSpine
