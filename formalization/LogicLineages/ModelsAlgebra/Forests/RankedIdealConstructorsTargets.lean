module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealConstructorsDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealConstructors.Targets
open RankedParse RankedIdealContext RankedGraphImage

def ProductIdeal : Prop := ∀ o I J, IsIdeal I → IsIdeal J → IsIdeal (product o I J)

def LinearPieceIdeal : Prop := ∀ K B, IsIdeal B → IsIdeal (linearPiece K B)

/-- Side terms are retained by diving into an actual filled context; no ideal
assumption is needed on the independently chosen side languages. -/
def ContextSupport : Prop := ∀ K B c b s, K c → B b → Homeomorphic s (plug c b) →
  linearPiece K B s
end LogicLineages.ModelsAlgebra.Forests.RankedIdealConstructors.Targets
