module
public import LogicLineages.OrdinalComparison.WWSourceScalarHeadProfileDefinitions

@[expose] public section
namespace LogicLineages.StandardControlCurrent.SourcePolynomialTargets
open OrdinalComparison OrdinalComparison.Source
open SourceClasses ForwardTranslation AdmissibleSum AdmissibleAssignment

/-- Complete current18 lem:source-polynomial. The source is the original
intrinsically typed term, not its normalized form. InternalLevelBound sees
all internal types and subtypes. The literal assignment and refusing scalar
compiler must actually succeed; every direct head, including nested tails,
is a genuine nonzero polynomial limit. No supplied assignment success or
polynomial-head oracle is assumed. -/
def PolynomialDirectHeads : Prop :=
  ∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
    ∀ (τ : Ty) (p : Policy) (t : OriginalTerm Γ τ), InternalLevelBound 2 t →
      ∃ v : OrdinalVector Γ τ.level, assignment p t = some v ∧
        ∃ s : Scalar (OrdinalComponent Γ), compileScalar (v 0) = some s ∧
          ∀ c ∈ scalarHeads s, Order.IsSuccLimit (fixedHead c) ∧
            fixedHead c < Ordinal.omega0 ^ Ordinal.omega0

end LogicLineages.StandardControlCurrent.SourcePolynomialTargets
