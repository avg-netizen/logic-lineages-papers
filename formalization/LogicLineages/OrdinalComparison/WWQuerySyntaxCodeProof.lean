module
public import LogicLineages.OrdinalComparison.WWQuerySyntaxCodeTargets
public import LogicLineages.OrdinalComparison.WWScalarSyntaxCodeProof
public import LogicLineages.OrdinalComparison.WWEncodedClosedPositiveProof
public import LogicLineages.OrdinalComparison.WWEncodedComparisonProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ForwardTranslation

theorem vectorSyntaxNormalizationCorrect : Targets.VectorSyntaxNormalizationCorrect := by
  intro ι n index v
  apply Prod.ext
  · exact scalarSyntaxNormalizationCorrect ι index v.scalar
  · simp only [normalizeVectorSyntaxCode, CompiledVector.syntaxCode, CompiledVector.code,
      normalCodes, CompiledVector.positiveNotes, List.map_ofFn]
    congr 1
    funext j
    exact encodedClosedPositiveCorrect (v.positive j)

theorem querySyntaxNormalizationCorrect : Targets.QuerySyntaxNormalizationCorrect := by
  intro ι n m index strict a b
  simp only [normalizeQuerySyntaxCode, compiledQuerySyntaxCode, compiledQueryCode,
    vectorSyntaxNormalizationCorrect ι n index a, vectorSyntaxNormalizationCorrect ι m index b]

private theorem vectorSyntaxNormalizerPrimitive : Primrec normalizeVectorSyntaxCode := by
  have hp : Primrec (fun v : EncodedVector => v.2.map encodedClosedPositive) :=
    Primrec.list_map Primrec.snd (encodedClosedPositivePrimitiveRecursive.comp Primrec.snd)
  exact (scalarSyntaxNormalizationPrimitiveRecursive.comp Primrec.fst).pair hp

theorem querySyntaxNormalizationPrimitiveRecursive : Targets.QuerySyntaxNormalizationPrimitiveRecursive := by
  exact Primrec.fst.pair ((vectorSyntaxNormalizerPrimitive.comp (Primrec.fst.comp Primrec.snd)).pair
    (vectorSyntaxNormalizerPrimitive.comp (Primrec.snd.comp Primrec.snd)))

theorem syntaxQueryComputable : Targets.SyntaxQueryComputable := by
  have heval : Computable (fun p : EncodedQuery × List Nat => encodedQueryAt p.1 p.2) := encodedQueryAtComputable
  apply (heval.comp ((querySyntaxNormalizationPrimitiveRecursive.to_comp.comp Computable.fst).pair Computable.snd)).of_eq
  intro p
  rfl
end LogicLineages.OrdinalComparison.Source.ForwardTranslation
