module
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeCheckDefinitions
public import LogicLineages.OrdinalComparison.ParametricSourceEraserDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceTypedCodeAdequacy
/-- This component adds no codec or semantics; it proves adequacy of the
existing typed erasure and source encoding in a fixed context. -/
abbrev SameCode {Γ τ} (t u : OriginalTerm Γ τ) : Prop := SyntaxCode.encodeTerm t=SyntaxCode.encodeTerm u
end LogicLineages.OrdinalComparison.Source.SourceTypedCodeAdequacy
