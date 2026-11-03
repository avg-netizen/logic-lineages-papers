module
public import LogicLineages.OrdinalComparison.LayeredComparison.FiniteGraphDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.FiniteGraph.Targets
/-- The real complete finite graph, including duplicated child occurrences,
is uniformly computable from actual computable numerical interfaces. -/
def UniformGraph : Prop:=∀ (A B:Type) [Primcodable A] [Primcodable B] [DecidableEq A]
  (children:A→List A) (assemble:A→List B→B) (μ:A→Nat),
  Computable children→Computable₂ assemble→Computable μ→
  Computable₂ (graph children assemble μ)
/-- The WHOLE bounded-depth graph evaluates to the true recursive value.
The source compiler's occurrence-count measure is explicitly computable;
no recursive-call or termination oracle is assumed. -/
def ExactDecreasingGraph : Prop:=∀ (A B:Type) [Primcodable A] [Primcodable B] [DecidableEq A] [Inhabited B]
  (children:A→List A) (assemble:A→List B→B) (μ:A→Nat),
  Computable children→Computable₂ assemble→Computable μ→
  ∀ f:A→B,(∀a,∀b∈children a,μ b<μ a)→
  (∀a,f a=assemble a ((children a).map f))→
  (∀a,graph children assemble μ a (μ a+1)=[(a,f a)])∧Computable f
end LogicLineages.OrdinalComparison.LayeredComparison.FiniteGraph.Targets
