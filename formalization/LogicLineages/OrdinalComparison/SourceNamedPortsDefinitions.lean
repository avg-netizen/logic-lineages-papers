module
public import LogicLineages.OrdinalComparison.SourceNamedWeakeningDefinitions
public import LogicLineages.OrdinalComparison.SourcePortContextsDefinitions
@[expose] public section
/-! Literal source-name spelling for finite port IDs, plus actual named context
weakening. This does not assume a named readback of arbitrary kernel observations
or named lambda-opening equality; those require their own provenance bridge. -/
namespace LogicLineages.OrdinalComparison.Source.SourceNamedPorts
open SourceNamedSyntax SourceNamedWeakening SourcePortContexts

def spellPort (Γ : Context) {B : Nat} (i : Fin B) : Nat := freshName Γ + i.val

def realizedContext (Γ : Context) {B : Nat} (P : PortContext B) : Context :=
  (P.map fun p => (spellPort Γ p.1, p.2)) ++ Γ

end LogicLineages.OrdinalComparison.Source.SourceNamedPorts
