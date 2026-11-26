module
public import LogicLineages.StandardControlCurrent.PolicyFiniteClassProof
public import LogicLineages.OrdinalComparison.WWSourceClassesFullProof
public import LogicLineages.StandardControlCurrent.PolicySourceInterfaceProof
public import LogicLineages.OrdinalComparison.LevelTwoCounterexample.SourceProof
public import LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.SourceMetadataProof
public import LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.TypedDecisionProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyFiniteProof
open OrdinalComparison Source Source.ForwardTranslation Source.SourceClasses Source.AdmissibleSum PolynomialGraphCompletion
open LevelTwoCounterexample
open LevelTwoDecisionCompletion.MetadataProof
theorem numeric_counterexamples (p : Policy) (Γ : List Ty) (hΓ : ∀ σ ∈ Γ,σ=Ty.ground)
    (τ υ : Ty) (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ)
    (hla : PolicyFinite.FiniteSource p a) (hlb : PolicyFinite.FiniteSource p b) (mode : Nat) :
    ∃ (av : OrdinalVector Γ τ.level) (bv : OrdinalVector Γ υ.level) (pack : Pair.Package),
      AdmissibleAssignment.assignment p a=some av ∧ AdmissibleAssignment.assignment p b=some bv ∧
      PolicyLevelTwo.compile p (Γ.length,mode,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b)=some pack ∧
      LevelTwoDecisionCompletion.PackageCertified pack ∧
      (Pair.Closed pack ↔ ∃ ρ : OrdinalComponent Γ → Nat, (∀ c,0<ρ c) ∧ ¬SourceCode.sourceRelation mode av bv ρ) := by
  obtain ⟨av, hav, ac, hac, _⟩ :=
    actualSourceVectorCompilation Γ hΓ τ p a
  obtain ⟨bv, hbv, bc, hbc, _⟩ :=
    actualSourceVectorCompilation Γ hΓ υ p b
  let ae := scalarExpr SourceCode.rawIndex ac.scalar
  let be := scalarExpr SourceCode.rawIndex bc.scalar
  let flag := SourceCode.positiveFlag mode (ac.syntaxCode SourceCode.rawIndex)
    (bc.syntaxCode SourceCode.rawIndex)
  have hae : ValidExpr ae := ScalarProof.validPolynomialExpression _ _ _
    (finite_polynomial ac.scalar ((finite_compiled av ac hav hac).mp hla))
  have hbe : ValidExpr be := ScalarProof.validPolynomialExpression _ _ _
    (finite_polynomial bc.scalar ((finite_compiled bv bc hbv hbc).mp hlb))
  have hfa : Fresh Γ.length ae := scalar_fresh ac.scalar
  have hfb : Fresh Γ.length be := scalar_fresh bc.scalar
  have hva (ν : Nat → Nat) : ae.value ν = ac.scalar.value (fun c => ν (SourceCode.rawIndex c)) :=
    ScalarProof.exactScalarValue (OrdinalComponent Γ) SourceCode.rawIndex ac.scalar ν
  have hvb (ν : Nat → Nat) : be.value ν = bc.scalar.value (fun c => ν (SourceCode.rawIndex c)) :=
    ScalarProof.exactScalarValue (OrdinalComponent Γ) SourceCode.rawIndex bc.scalar ν
  refine ⟨av, bv, Pair.package Γ.length mode flag ae be, hav, hbv, ?_, literalPackageMetadata Γ.length mode flag ae be hae hbe hfa hfb, ?_⟩
  · unfold PolicyLevelTwo.compile
    rw [PolicySourceInterfaceProof.code hΓ a av ac hav hac,
      PolicySourceInterfaceProof.code hΓ b bv bc hbv hbc]
    simp only [Option.bind_some]
    change some (Pair.Code.package (Γ.length, mode, flag,
      ScalarCode.lowerSyntax (scalarSyntaxCode SourceCode.rawIndex ac.scalar),
      ScalarCode.lowerSyntax (scalarSyntaxCode SourceCode.rawIndex bc.scalar))) =
        some (Pair.package Γ.length mode flag ae be)
    rw [(ScalarCodeProof.literalScalarCode _ SourceCode.rawIndex ac.scalar).2,
      (ScalarCodeProof.literalScalarCode _ SourceCode.rawIndex bc.scalar).2,
      PairCodeProof.literalNumericPackage]
  · rw [PairProof.exactCounterexample Γ.length mode flag ae be hae hbe hfa hfb]
    constructor
    · rintro ⟨ν, hν, hbad⟩
      refine ⟨fun c => ν (SourceCode.rawIndex c),
        fun c => hν _ (raw_index_bound c), ?_⟩
      intro hs
      apply hbad
      have h := (SourceProof.source_relation mode av bv ac bc hac hbc
        (fun c => ν (SourceCode.rawIndex c))).mpr hs
      rw [hva ν, hvb ν]
      exact h
    · rintro ⟨ρ, hρ, hbad⟩
      obtain ⟨xs, _, hxs⟩ := groundPositiveTupleComplete Γ hΓ ρ hρ
      let ν : Nat → Nat := fun i => xs.getD i 0 + 1
      have hρν : (fun c => ν (SourceCode.rawIndex c)) = ρ := by
        funext c
        exact hxs c
      refine ⟨ν, fun _ _ => Nat.zero_lt_succ _, ?_⟩
      intro h
      apply hbad
      apply (SourceProof.source_relation mode av bv ac bc hac hbc ρ).mp
      rw [hva ν, hvb ν, hρν] at h
      exact h

end LogicLineages.StandardControlCurrent.PolicyFiniteProof
