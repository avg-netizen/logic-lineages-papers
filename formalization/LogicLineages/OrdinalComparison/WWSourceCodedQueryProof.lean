module
public import LogicLineages.OrdinalComparison.WWSourceCodedQueryTargets
public import LogicLineages.OrdinalComparison.WWSourceComparisonProof
public import LogicLineages.OrdinalComparison.WWEncodedCounterBoundProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ForwardTranslation

theorem actualSourceCodedQuery : Targets.ActualSourceCodedQuery := by
  intro Γ hΓ τ υ p strict a b
  obtain ⟨av, bv, q, hav, hbv, hq, hp, hall⟩ :=
    actualSourceQueryCompilation Γ hΓ τ υ p strict a b
  let code := Encodable.encode (Γ.length, q)
  have hd : decodeArityQuery code = (Γ.length, q) := encodedQueryCodecCorrect.1 _
  refine ⟨av, bv, code, hav, hbv, ?_, ?_, ?_⟩
  · simp [compileSourceCode, hq, code]
  · simp only [queryArity, hd]
  · simpa only [CodedQueryGood, queryArity, codedQueryAt, hd] using hall
end LogicLineages.OrdinalComparison.Source.ForwardTranslation
