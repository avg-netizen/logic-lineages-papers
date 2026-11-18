import LogicLineages.PersistentMarking.Grafting
namespace LogicLineages.PersistentMarking.GraftingTargets
open Spine NameBridge TypeSupport Grafting

def SingleMapTyping : Prop := ∀ σ x p, Typed EmptyContext p σ → FreeMapTyped EmptyContext (singleMap σ x p)

def TypedNamedSubstitutionEncoding : Prop := ∀ η A τ, NamedMapTyped η → NamedTyped A τ →
  encode [] (namedSubstitute η A) = freeSub (encodeMap η) 0 (encode [] A)

def TemplateGrafting : Prop := ∀ S A τ σ x p q,
  PaperTerm S A τ → Ordinary A → PaperTerm S p σ → PaperTerm S q σ → Weak S p q →
  Weak S (freeSub (singleMap σ x p) 0 A) (freeSub (singleMap σ x q) 0 A)

def NamedTemplateGrafting : Prop := ∀ S A τ σ x p q,
  NamedTyped A τ → NamedValid S A → StructuralCoverageTargets.NamedOrdinary A →
  NamedTyped p σ → NamedValid S p → NamedTyped q σ → NamedValid S q →
  Weak S (encode [] p) (encode [] q) →
  Weak S (encode [] (namedSubstitute (singleNamedMap σ x p) A))
    (encode [] (namedSubstitute (singleNamedMap σ x q) A))

def FullGrafting : Prop := TemplateGrafting ∧ NamedTemplateGrafting
end LogicLineages.PersistentMarking.GraftingTargets
