module
public import LogicLineages.OrdinalComparison.SourceUnaryChainDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceUnaryChain.Targets
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

/-- Whole paper09 source-realization.tex lem:chain. The aligned list contains
actual full-default source assignments, not hypothetical operator heads.
All real operator scalars are retained in the chain construction. One fresh
binder, empty lists, arbitrary original unary sources and shared valuations
are explicit. The ordinal identity is stronger than its admissible/unit
instances and assumes no carrier or child-construction certificate. -/
def FullSourceUnaryChain : Prop :=
  ∀ (Γ : List Ty) (vs : List (OriginalTerm Γ (.arrow .ground .ground))),
    ∃ ws : List (OrdinalVector Γ 1),
      List.Forall₂ (fun v w => AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy v = some w) vs ws ∧
      ∃ u : OrdinalVector Γ 1,
        AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (chainSource vs) = some u ∧
        ∀ ν : OrdinalComponent Γ → Ordinal, denote ν (u 1) = headSum ν ws
end LogicLineages.OrdinalComparison.Source.SourceUnaryChain.Targets
