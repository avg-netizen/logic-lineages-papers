module
public import LogicLineages.OrdinalComparison.WWEncodedScalarTargets
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentDefinitions
public import LogicLineages.OrdinalComparison.SourceTypedPortsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open ForwardTranslation AdmissibleSum AdmissibleAssignment
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

/-- Actual ground-tuple evaluation of every canonical scalar coordinate via
the explicit numeric compiler code and genuine uniform evaluator. Input
positions are the original context positions, never independent copies of
repeated occurrences. Source syntax coding and whole-query search remain
separate from this supplier. -/
def ActualSourceTupleEvaluation : Prop :=
  EncodedScalarComputable ∧
  ∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
    ∀ (τ : Ty) (p : Policy) (t : OriginalTerm Γ τ),
      ∃ v : OrdinalVector Γ τ.level, assignment p t = some v ∧
        ∃ s : Scalar (OrdinalComponent Γ), compileScalar (v 0) = some s ∧
          ∀ xs : List Nat,
            (encodedScalarValue
              (scalarCode (fun c => SourceTypedPorts.variableIndex c.2.1) s) xs : Ordinal) =
              denote (fun c => ((xs.getD (SourceTypedPorts.variableIndex c.2.1) 0 + 1 : Nat) : Ordinal)) (v 0)
end LogicLineages.OrdinalComparison.Source.Targets
