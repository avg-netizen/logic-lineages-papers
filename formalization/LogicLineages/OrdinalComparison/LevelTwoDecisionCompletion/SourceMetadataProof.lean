module
public import LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.Targets
public import LogicLineages.OrdinalComparison.LevelTwoCounterexample.AdmissionProof
public import LogicLineages.OrdinalComparison.LevelTwoCounterexample.ScalarProof
public import LogicLineages.OrdinalComparison.LevelTwoCounterexample.ScalarCodeProof
public import LogicLineages.OrdinalComparison.LevelTwoCounterexample.PairProof
public import LogicLineages.OrdinalComparison.LevelTwoCounterexample.PairCodeProof
public import LogicLineages.OrdinalComparison.WWGroundPositiveQuerySplitProof
public import LogicLineages.OrdinalComparison.SourceTypedPortsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.MetadataProof
open Source Source.ForwardTranslation Source.SourceClasses
open PolynomialGraphCompletion LevelTwoCounterexample

/-- Original component labels are the original context indices. -/
theorem raw_index_bound {Γ : List Ty} (c : OrdinalComponent Γ) :
    SourceCode.rawIndex c < Γ.length :=
  SourceTypedPortsProof.typedVariableIndex.1 Γ c.1 c.2.1

theorem scalar_fresh {Γ : List Ty} (s : Scalar (OrdinalComponent Γ)) :
    Fresh Γ.length (scalarExpr SourceCode.rawIndex s) := by
  intro i hi
  rw [ScalarProof.exactOriginalNames] at hi
  obtain ⟨c,_,rfl⟩ := List.mem_map.mp hi
  exact raw_index_bound c

/-- Projection from the actual successful vector compilation, not a new
choice of scalar expression. -/
theorem compiled_scalar {Γ : List Ty} {n : Nat} (v : OrdinalVector Γ n)
    (c : CompiledVector (OrdinalComponent Γ) n) (hc : compileVector v = some c) :
    compileScalar (v 0) = some c.scalar := by
  obtain ⟨s,hs,p,_,he⟩ : ∃ s, compileScalar (v 0) = some s ∧
      ∃ p, AdmissibleAssignment.collect n (fun j => extractPositive (v j.succ)) = some p ∧
        (CompiledVector.mk s p) = c := by
    simpa only [compileVector,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] using hc
  subst c
  exact hs

/-- The accepted original-source scalar theorem supplies validity; both
successful deterministic compilers identify its scalar with the emitted one. -/
theorem compiled_valid {Γ : List Ty} (hΓ : ∀ σ ∈ Γ, σ = Ty.ground)
    {τ : Ty} (t : OriginalTerm Γ τ) (ht : InternalLevelBound 2 t)
    (v : OrdinalVector Γ τ.level) (c : CompiledVector (OrdinalComponent Γ) τ.level)
    (hv : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t = some v)
    (hc : compileVector v = some c) : ValidExpr (scalarExpr SourceCode.rawIndex c.scalar) := by
  obtain ⟨w,s,hw,hs,hvalid,_⟩ := ScalarProof.actualLevelTwoScalar Γ hΓ τ
    OrdinalSyntax.defaultPolicy t ht SourceCode.rawIndex
  rw [hv] at hw
  cases Option.some.inj hw
  have he : s = c.scalar := Option.some.inj (hs.symm.trans (compiled_scalar v c hc))
  subst s
  exact hvalid

/-- Literal package shape, derived independently of the counterexample
semantic equivalence. No emitted metadata is presumed. -/
theorem typed_package_shape (Γ : List Ty) (hΓ : ∀ σ ∈ Γ, σ = Ty.ground)
    (τ υ : Ty) (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ)
    (hla : InternalLevelBound 2 a) (hlb : InternalLevelBound 2 b) (mode : Nat) :
    ∃ (flag : Bool) (ae be : Expr),
      ValidExpr ae ∧ ValidExpr be ∧ Fresh Γ.length ae ∧ Fresh Γ.length be ∧
      SourceCode.compile (Γ.length,mode,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b) =
        some (Pair.package Γ.length mode flag ae be) := by
  obtain ⟨av,hav,ac,hac,_⟩ :=
    actualSourceVectorCompilation Γ hΓ τ OrdinalSyntax.defaultPolicy a
  obtain ⟨bv,hbv,bc,hbc,_⟩ :=
    actualSourceVectorCompilation Γ hΓ υ OrdinalSyntax.defaultPolicy b
  let ae := scalarExpr SourceCode.rawIndex ac.scalar
  let be := scalarExpr SourceCode.rawIndex bc.scalar
  let flag := SourceCode.positiveFlag mode (ac.syntaxCode SourceCode.rawIndex)
    (bc.syntaxCode SourceCode.rawIndex)
  refine ⟨flag,ae,be,compiled_valid hΓ a hla av ac hav hac,
    compiled_valid hΓ b hlb bv bc hbv hbc,scalar_fresh ac.scalar,scalar_fresh bc.scalar,?_⟩
  unfold SourceCode.compile
  rw [GroundPositiveQuerySplit.Proof.vectorAt_typed hΓ a av ac hav hac,
    GroundPositiveQuerySplit.Proof.vectorAt_typed hΓ b bv bc hbv hbc]
  simp only [Option.bind_some]
  change some (Pair.Code.package (Γ.length,mode,flag,
    ScalarCode.lowerSyntax (scalarSyntaxCode SourceCode.rawIndex ac.scalar),
    ScalarCode.lowerSyntax (scalarSyntaxCode SourceCode.rawIndex bc.scalar))) =
      some (Pair.package Γ.length mode flag ae be)
  rw [(ScalarCodeProof.literalScalarCode _ SourceCode.rawIndex ac.scalar).2,
    (ScalarCodeProof.literalScalarCode _ SourceCode.rawIndex bc.scalar).2,
    PairCodeProof.literalNumericPackage]

theorem emittedPackageShape : Targets.EmittedPackageShape := by
  intro q p hp
  have haccept : Admission.accepts q = true := by
    have h := (AdmissionProof.exactGuardedDomain q).1
    rw [hp] at h
    exact h.symm
  obtain ⟨τ,υ,a,b,ha,hb,hla,hlb⟩ := (AdmissionProof.exactGroundClass q).mp haccept
  obtain ⟨flag,ae,be,hva,hvb,hfa,hfb,hcompiled⟩ :=
    typed_package_shape (List.replicate q.1 Ty.ground)
      (fun _ hs => List.eq_of_mem_replicate hs) τ υ a b hla hlb q.2.1
  have hc : SourceCode.compile q = some p := by
    rw [← (AdmissionProof.exactGuardedDomain q).2.2 haccept]
    exact hp
  have hc' : SourceCode.compile q = some (Pair.package q.1 q.2.1 flag ae be) := by
    simpa only [List.length_replicate,ha,hb] using hcompiled
  refine ⟨flag,ae,be,hva,hvb,?_,?_,(Option.some.inj (hc'.symm.trans hc)).symm⟩
  · simpa only [List.length_replicate] using hfa
  · simpa only [List.length_replicate] using hfb

theorem literalPackageMetadata : Targets.LiteralPackageMetadata := by
  intro n mode flag a b ha hb hfa hfb
  have hd := PairProof.exactDomainsAndDegree n mode flag a b ha hb
  have hs := PairProof.exactClosedSupport n mode flag a b hfa hfb
  refine ⟨hd.1,hs.1,?_,fun r hr => ⟨(hd.2.1 r hr).1,hs.2.2.1 r hr⟩,
    hd.2.2.1,hs.2.2.2.1⟩
  intro i hi
  change i < n at hi
  change i ∈ List.range (n+nodeCount (.add a b))
  apply List.mem_range.mpr
  omega

theorem emittedPackageMetadata : Targets.EmittedPackageMetadata := by
  intro q p hp
  obtain ⟨flag,a,b,ha,hb,hfa,hfb,he⟩ := emittedPackageShape q p hp
  rw [he]
  exact literalPackageMetadata q.1 q.2.1 flag a b ha hb hfa hfb

#print axioms raw_index_bound
#print axioms scalar_fresh
#print axioms compiled_scalar
#print axioms compiled_valid
#print axioms typed_package_shape
#print axioms emittedPackageShape
#print axioms literalPackageMetadata
#print axioms emittedPackageMetadata

end LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.MetadataProof
