module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LiteralFiniteSourceTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticFiniteVectorProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LiteralFiniteSourceProof
open LiteralFiniteSource Source Source.ForwardTranslation

theorem acceptsSource_computable : Computable Code.acceptsSource := by
  have hscalar : Computable (fun p : (Nat × Nat) × EncodedVector =>
      SemanticFiniteScalar.Code.compile p.2.1) :=
    SemanticFiniteScalarProgram.compile_computable.comp
      (Computable.fst.comp Computable.snd)
  exact Primrec.option_isSome.to_comp.comp
    (Computable.option_bind GroundPositiveQuerySplit.Proof.vectorAt_primitive.to_comp
      hscalar.to₂)

theorem actualNumericPrograms : LiteralFiniteSourceTargets.ActualNumericPrograms :=
  ⟨acceptsSource_computable, SemanticFiniteVectorProgram.source_computable⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LiteralFiniteSourceProof
