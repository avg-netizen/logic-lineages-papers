module
public import LogicLineages.ModelsAlgebra.Forests.RankedParseDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealContext
open RankedParse
/-- Ordered one-hole contexts; the other child is an actual ranked term. -/
inductive Context where
  | hole
  | left (o : Operation) (c : Context) (right : Term)
  | right (o : Operation) (left : Term) (c : Context)

def plug : Context → Term → Term
  | .hole, t => t
  | .left o c r, t => .node o (plug c t) r
  | .right o l c, t => .node o l (plug c t)

def compose : Context → Context → Context
  | .hole, d => d
  | .left o c r, d => .left o (compose c d) r
  | .right o l c, d => .right o l (compose c d)
end LogicLineages.ModelsAlgebra.Forests.RankedIdealContext
