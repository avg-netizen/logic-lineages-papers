module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealContextDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealContext.Targets
open RankedParse

def EmbeddingReflexive : Prop := ∀ t, Homeomorphic t t

def EmbeddingTransitive : Prop := ∀ {s t u}, Homeomorphic s t → Homeomorphic t u → Homeomorphic s u

def PlugMonotone : Prop := ∀ c {s t}, Homeomorphic s t → Homeomorphic (plug c s) (plug c t)

def HoleEmbeds : Prop := ∀ c t, Homeomorphic t (plug c t)

def PlugComposition : Prop := ∀ c d t, plug (compose c d) t = plug c (plug d t)
end LogicLineages.ModelsAlgebra.Forests.RankedIdealContext.Targets
