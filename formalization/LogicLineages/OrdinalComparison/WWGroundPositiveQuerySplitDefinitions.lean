module
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentDefinitions
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxVectorCompilerDefinitions
public import LogicLineages.OrdinalComparison.WWOriginalDomainDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundPositiveQuerySplit
open ForwardTranslation
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

/-- Literal numeric default-policy assignment and vector extraction. The
source code is unchanged; only its external all-ground context is supplied. -/
def vectorAt (p : Nat × Nat) : Option EncodedVector :=
  (DefaultSourceAssignment.assignmentCode
    (List.replicate p.1 (SyntaxCode.typeCode Ty.ground)) p.2).bind OrdinalSyntax.compileVectorCode

/-- Closed positive syntax is actually normalized before comparing the
normal-note codes. Failed raw syntax/compilation explicitly returns false. -/
def positiveFlagCode (p : Nat × Nat × Nat) : Bool :=
  ((vectorAt (p.1,p.2.1)).bind (fun a =>
    (vectorAt (p.1,p.2.2)).map (fun b =>
      positiveComparison (a.2.map encodedClosedPositive) (b.2.map encodedClosedPositive)))).getD false

/-- The actual full-assignment scalar, not a supplied scalar oracle. The
zero fallback is proved unreachable for every typed source in the targets. -/
noncomputable def scalarValue {Γ τ} (ρ : OrdinalComponent Γ → Nat) (t : OriginalTerm Γ τ) : Nat :=
  ((AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t).map (fun v =>
    OriginalDomain.finiteValue (denote (fun c => ((ρ c+1 : Nat) : Ordinal)) (v 0)))).getD 0

noncomputable def QueryAt {Γ τ υ} (strict : Bool) (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ)
    (ρ : OrdinalComponent Γ → Nat) : Prop :=
  ∃ (av : OrdinalVector Γ τ.level) (bv : OrdinalVector Γ υ.level),
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy a=some av ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy b=some bv ∧
    SourceComparisonAt strict av bv (fun c => ρ c+1)
end LogicLineages.OrdinalComparison.Source.GroundPositiveQuerySplit
