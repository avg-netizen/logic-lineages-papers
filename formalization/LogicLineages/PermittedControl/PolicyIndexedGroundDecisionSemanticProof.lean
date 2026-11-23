module
public import LogicLineages.PermittedControl.PolicyIndexedGroundDecisionTargets
import LogicLineages.PermittedControl.GroundComparisonReductionProof
import LogicLineages.PermittedControl.GroundComparisonPositiveProof
import LogicLineages.PermittedControl.SelectedGeneratedSourceProof
import LogicLineages.OrdinalComparison.WWScalarSyntaxCodeProof

public section
namespace LogicLineages.PermittedControl.PolicyIndexedGroundDriver
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax Source.ForwardTranslation
open SelectedSourceDomain SelectedGeneratedSource
open GroundComparison (Relation Canonical)
open GroundComparisonReduction (tagOf equalFlag exactCanonicalReduction)
open GroundComparisonPositive (positiveTest)
open GroundComparisonAssembly (QueryInterface)

attribute [local irreducible] StandardControlCurrent.PolicySourceInterface.compile

theorem pointwiseDecisionCorrect (query : Query) (hq : QueryInterface query)
    (ctrl : Nat → Nat) (K : Nat) (hsel : SelectedWithThreshold ctrl K)
    (p : Policy) (rel : Relation) (cbd : Block)
    (hdec : ∀ (known : List Nat) (gs : List OriginalPrintedCircuitSequential.Gate)
      (pf : NormalForm.Formula), OriginalPrintedCircuitSequential.Topological known gs →
      PreparedProjection.PlainPreparedFormula pf →
      ∀ b : Bool, cbd (OriginalPrintedRawFamilyFrontend.encodeInput known gs pf b) = some true ↔
        OriginalPrintedTypedExistential.HasSuccessfulObservation ctrl gs pf b)
    :
    ∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) → ∀ (τ υ : Ty)
      (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ),
      pointwiseDecision p cbd query rel (Γ.length,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b) = true ↔
        Canonical ctrl p rel a b := by
  intro Γ hΓ τ υ a b
  obtain ⟨va,ca,ha,_,hca,_,hva,_⟩ := SelectedGeneratedSourceProof.typedImage ctrl K hsel p Γ hΓ τ a
  obtain ⟨vb,cb,hb,_,hcb',_,hvb,_⟩ := SelectedGeneratedSourceProof.typedImage ctrl K hsel p Γ hΓ υ b
  have red := exactCanonicalReduction ctrl K hsel p Γ hΓ τ υ a b va vb ca cb ha hb hva hvb rel
  obtain ⟨known,gs,pf,htop,hplain,hqeq,hsem⟩ :=
    hq (tagOf rel) (fun x : OrdinalComponent Γ => SourceTypedPorts.variableIndex x.2.1) ca.scalar cb.scalar
  have hcbt := hdec known gs pf htop hplain true
  have na := scalarSyntaxNormalizationCorrect (OrdinalComponent Γ)
    (fun x : OrdinalComponent Γ => SourceTypedPorts.variableIndex x.2.1) ca.scalar
  have nb := scalarSyntaxNormalizationCorrect (OrdinalComponent Γ)
    (fun x : OrdinalComponent Γ => SourceTypedPorts.variableIndex x.2.1) cb.scalar
  have step : pointwiseDecision p cbd query rel (Γ.length,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b) =
      body cbd query rel (ca.syntaxCode (fun x => SourceTypedPorts.variableIndex x.2.1))
        (cb.syntaxCode (fun x => SourceTypedPorts.variableIndex x.2.1)) := by
    unfold pointwiseDecision
    rw [hca,hcb']
    rfl
  rw [step,red]
  unfold body
  change (positiveTest (equalFlag rel) (List.ofFn (fun j => closedPositiveCode (ca.positive j)))
      (List.ofFn (fun j => closedPositiveCode (cb.positive j))) &&
    !(decide (cbd (query (tagOf rel)
      (normalizeScalarSyntaxCode (scalarSyntaxCode (fun x : OrdinalComponent Γ => SourceTypedPorts.variableIndex x.2.1) ca.scalar))
      (normalizeScalarSyntaxCode (scalarSyntaxCode (fun x : OrdinalComponent Γ => SourceTypedPorts.variableIndex x.2.1) cb.scalar))) =
        some true))) = true ↔ _
  rw [na,nb,hqeq,List.map_ofFn,List.map_ofFn,Bool.and_eq_true,Bool.not_eq_true',decide_eq_false_iff_not,hcbt,
    hsem ctrl K hsel]
  rfl

#print axioms pointwiseDecisionCorrect
end LogicLineages.PermittedControl.PolicyIndexedGroundDriver
