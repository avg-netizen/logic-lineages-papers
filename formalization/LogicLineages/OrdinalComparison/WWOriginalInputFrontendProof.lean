module
public import LogicLineages.OrdinalComparison.WWOriginalInputFrontendTargets
public import LogicLineages.OrdinalComparison.WWOriginalInputDomainProof
public import LogicLineages.OrdinalComparison.WWOriginalInputFrontendComputability
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentSemanticProof
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxVectorCompilerProof
public import LogicLineages.OrdinalComparison.WWQuerySyntaxCodeProof
public import LogicLineages.OrdinalComparison.WWSourceComparisonProof
public import LogicLineages.OrdinalComparison.WWEncodedCounterBoundProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalInput
open ForwardTranslation OrdinalSyntax

private theorem context_ground (q : Query) : ∀ σ ∈ context q, σ=Ty.ground := by
  intro σ hσ
  exact (List.mem_replicate.mp hσ).2

private theorem compilation (q : Query) {τ υ : Ty}
    (a : OriginalTerm (context q) τ) (b : OriginalTerm (context q) υ)
    (ha : SyntaxCode.encodeTerm a=q.2.2.1) (hb : SyntaxCode.encodeTerm b=q.2.2.2) :
    ∃ av : OrdinalVector (context q) τ.level, ∃ bv : OrdinalVector (context q) υ.level,
    ∃ ac : CompiledVector (OrdinalComponent (context q)) τ.level,
    ∃ bc : CompiledVector (OrdinalComponent (context q)) υ.level,
      AdmissibleAssignment.assignment defaultPolicy a=some av ∧
      AdmissibleAssignment.assignment defaultPolicy b=some bv ∧
      compileVector av=some ac ∧ compileVector bv=some bc ∧
      compileSyntax q=some (compiledQuerySyntaxCode (fun c => SourceTypedPorts.variableIndex c.2.1) q.2.1 ac bc) := by
  obtain ⟨av,hav,ac,hac,_⟩ := actualSourceVectorCompilation (context q) (context_ground q) τ defaultPolicy a
  obtain ⟨bv,hbv,bc,hbc,_⟩ := actualSourceVectorCompilation (context q) (context_ground q) υ defaultPolicy b
  have hna := DefaultSourceAssignment.Proof.assignmentCorrect (context q) τ a
  have hnb := DefaultSourceAssignment.Proof.assignmentCorrect (context q) υ b
  rw [hav, ha] at hna
  rw [hbv, hb] at hnb
  have hctx : (context q).map SyntaxCode.typeCode = List.replicate q.1 0 := by simp [context, SyntaxCode.typeCode]
  rw [hctx] at hna hnb
  simp only [Option.map_some] at hna hnb
  have hva := ordinalSyntaxVectorCompilerCorrect (context q) τ.level av
  have hvb := ordinalSyntaxVectorCompilerCorrect (context q) υ.level bv
  rw [hac] at hva
  rw [hbc] at hvb
  refine ⟨av,bv,ac,bc,hav,hbv,hac,hbc,?_⟩
  simp only [Option.map_some] at hva hvb
  simp only [compileSyntax, hna, hnb]
  change ((compileVectorCode (vectorCode av)).bind (fun ac0 =>
    (compileVectorCode (vectorCode bv)).bind (fun bc0 => some (q.2.1, ac0, bc0)))) = _
  rw [hva, hvb]
  rfl

private theorem source_point (q : Query) (xs : List Nat) {τ υ : Ty}
    (a : OriginalTerm (context q) τ) (b : OriginalTerm (context q) υ)
    (av : OrdinalVector (context q) τ.level) (bv : OrdinalVector (context q) υ.level)
    (ha : SyntaxCode.encodeTerm a=q.2.2.1) (hb : SyntaxCode.encodeTerm b=q.2.2.2)
    (hav : AdmissibleAssignment.assignment defaultPolicy a=some av)
    (hbv : AdmissibleAssignment.assignment defaultPolicy b=some bv)
    (k : EncodedQuery) (hk : compileSyntax q=some k) :
    encodedQueryAt (normalizeQuerySyntaxCode k) xs=true ↔
      SourceComparisonAt q.2.1 av bv (fun c => xs.getD (SourceTypedPorts.variableIndex c.2.1) 0+1) := by
  obtain ⟨av',bv',ac,bc,hav',hbv',hac,hbc,hk'⟩ := compilation q a b ha hb
  have ea : av'=av := Option.some.inj (hav'.symm.trans hav)
  have eb : bv'=bv := Option.some.inj (hbv'.symm.trans hbv)
  subst av' bv'
  have ek : k=compiledQuerySyntaxCode (fun c => SourceTypedPorts.variableIndex c.2.1) q.2.1 ac bc :=
    Option.some.inj (hk.symm.trans hk')
  rw [ek, querySyntaxNormalizationCorrect]
  exact compiledQueryPointCorrect (context q) τ.level υ.level av bv ac bc hac hbc _ q.2.1 xs

private theorem syntax_some_witness (q : Query) (k : EncodedQuery) (hk : compileSyntax q=some k) :
    ∃ (τ υ : Ty) (a : OriginalTerm (context q) τ) (b : OriginalTerm (context q) υ)
      (av : OrdinalVector (context q) τ.level) (bv : OrdinalVector (context q) υ.level),
      SyntaxCode.encodeTerm a=q.2.2.1 ∧ SyntaxCode.encodeTerm b=q.2.2.2 ∧
      AdmissibleAssignment.assignment defaultPolicy a=some av ∧
      AdmissibleAssignment.assignment defaultPolicy b=some bv := by
  unfold compileSyntax at hk
  obtain ⟨avc,havc,hr⟩ := Option.bind_eq_some_iff.mp hk
  obtain ⟨bvc,hbvc,_⟩ := Option.bind_eq_some_iff.mp hr
  have ha : DefaultSourceAssignment.assignmentCode ((context q).map SyntaxCode.typeCode) q.2.2.1=some avc := by
    simpa [context, SyntaxCode.typeCode] using havc
  have hb : DefaultSourceAssignment.assignmentCode ((context q).map SyntaxCode.typeCode) q.2.2.2=some bvc := by
    simpa [context, SyntaxCode.typeCode] using hbvc
  obtain ⟨τ,a,av,hea,haa,_⟩ := (DefaultSourceAssignment.Proof.assignmentSourceExact (context q) q.2.2.1 avc).mp ha
  obtain ⟨υ,b,bv,heb,hbb,_⟩ := (DefaultSourceAssignment.Proof.assignmentSourceExact (context q) q.2.2.2 bvc).mp hb
  exact ⟨τ,υ,a,b,av,bv,hea,heb,haa,hbb⟩

private theorem raw_point (q : Query) (xs : List Nat) :
    encodedQueryAt (((compileSyntax q).map normalizeQuerySyntaxCode).getD trueQuery) xs=true ↔ Point q xs := by
  cases hk : compileSyntax q with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    have ht : encodedQueryAt trueQuery xs=true := by
      simp [trueQuery, encodedQueryAt, positiveComparison, positiveComparisonUpTo]
    rw [ht]
    constructor
    · intro _ τ υ a b av bv ha hb hav hbv
      obtain ⟨_,_,_,_,_,_,_,_,hs⟩ := compilation q a b ha hb
      rw [hk] at hs
      contradiction
    · intro _
      rfl
  | some k =>
    simp only [Option.map_some, Option.getD_some]
    constructor
    · intro h τ υ a b av bv ha hb hav hbv
      exact (source_point q xs a b av bv ha hb hav hbv k hk).mp h
    · intro h
      obtain ⟨τ,υ,a,b,av,bv,ha,hb,hav,hbv⟩ := syntax_some_witness q k hk
      exact (source_point q xs a b av bv ha hb hav hbv k hk).mpr (h τ υ a b av bv ha hb hav hbv)

theorem originalInputFrontendPointCorrect : Targets.OriginalInputFrontendPointCorrect := by
  intro n xs
  have hd := encodedQueryCodecCorrect.1 ((decode n).1, ((compileSyntax (decode n)).map normalizeQuerySyntaxCode).getD trueQuery)
  change decodeArityQuery (frontend n) = _ at hd
  simpa only [codedQueryAt, hd] using raw_point (decode n) xs

theorem originalInputFrontendGoodCorrect : Targets.OriginalInputFrontendGoodCorrect := by
  intro n
  have hd := encodedQueryCodecCorrect.1 ((decode n).1, ((compileSyntax (decode n)).map normalizeQuerySyntaxCode).getD trueQuery)
  change decodeArityQuery (frontend n) = _ at hd
  have harity : queryArity (frontend n) = (decode n).1 := by rw [queryArity, hd]
  change CodedQueryGood (frontend n) ↔ Good (decode n)
  rw [originalInputUniversalTupleEquivalence (decode n)]
  simp only [CodedQueryGood, harity, originalInputFrontendPointCorrect n]
end LogicLineages.OrdinalComparison.Source.OriginalInput
