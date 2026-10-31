module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularCodeDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularCode.Targets
open RankedParse RankedGraphImage RankedIdealComponents

def AtomExact : Prop := ∀ t, language atom t ↔ t = .atom

def AtomIdeal : Prop := IsIdeal (language atom)

def ComponentExact : Prop := ∀ C q t, language (component C q) t ↔ stateLanguage C.machine q t

def ProductExact : Prop := ∀ o A B t, language (product o A B) t ↔
  RankedIdealConstructors.product o (language A) (language B) t

def LinearExact : Prop := ∀ seed n (rules : Fin n → Rule) t, language (linear seed rules) t ↔
  RankedIdealConstructors.linearPiece (RankedIdealRegular.allowed (fun i => viewRule (rules i)))
    (language seed) t

def ProductIdeal : Prop := ∀ o A B, IsIdeal (language A) → IsIdeal (language B) →
  IsIdeal (language (product o A B))

def LinearIdeal : Prop := ∀ seed n (rules : Fin n → Rule), IsIdeal (language seed) →
  IsIdeal (language (linear seed rules))

def ComponentIdeal : Prop := ∀ C q, NonlinearAt C.machine q → IsIdeal (language (component C q))
end LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularCode.Targets
