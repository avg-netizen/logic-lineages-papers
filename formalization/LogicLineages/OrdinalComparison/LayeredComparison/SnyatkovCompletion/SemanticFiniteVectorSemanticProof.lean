module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticFiniteVectorTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticFiniteScalarSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticFiniteScalarCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.RecursorFreeVectorSemanticProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticFiniteVectorProof
open SemanticFiniteVector RecursorFreeVector Source Source.ForwardTranslation CommonLayerSyntax

private theorem vector_decision : ∀ (ι : Type) (index : ι → Nat) (n mode k l : Nat)
  (a : CompiledVector ι k) (b : CompiledVector ι l) ta tb,
  SemanticFiniteScalar.compile index a.scalar = some ta →
  SemanticFiniteScalar.compile index b.scalar = some tb →
  ∃ answer, SemanticFiniteVector.Code.decideVectors (n,mode,a.syntaxCode index,b.syntaxCode index) = some answer ∧
    ((∀ ν : Nat → Nat, (∀ i < n, 0 < ν i) → vectorRelation mode a b (fun i => ν (index i))) ↔
      answer = true) := by
  intro ι index n mode k l a b ta tb ha hb
  obtain ⟨answer,hd,hs⟩ := RecursorFreeVectorProof.closed_answer (formula n mode ta tb)
  let flag := positiveFlag mode (a.syntaxCode index) (b.syntaxCode index)
  refine ⟨flag && answer, ?_, ?_⟩
  · unfold SemanticFiniteVector.Code.decideVectors
    change (SemanticFiniteScalar.Code.compile (scalarSyntaxCode index a.scalar)).bind _ = _
    rw [SemanticFiniteScalarProof.literalNumericCalibration, ha]
    simp only [Option.map_some, Option.bind_some]
    change (SemanticFiniteScalar.Code.compile (scalarSyntaxCode index b.scalar)).bind _ = _
    rw [SemanticFiniteScalarProof.literalNumericCalibration, hb]
    simp only [Option.map_some, Option.bind_some]
    rw [(RecursorFreeVectorProof.exactFormula n mode ta tb).1, hd]
    rfl
  · have hsem : (∀ ν : Nat → Nat, (∀ i < n, 0 < ν i) →
        scalarRelation mode (a.scalar.value (fun i => ν (index i))) (b.scalar.value (fun i => ν (index i)))) ↔
        answer = true := by
      rw [← hs]
      apply forall_congr'
      intro ν
      rw [(RecursorFreeVectorProof.exactFormula n mode ta tb).2]
      rw [(SemanticFiniteScalarProof.actualScalar ι index a.scalar ta ha).1 ν,
        (SemanticFiniteScalarProof.actualScalar ι index b.scalar tb hb).1 ν]
    rw [Bool.and_eq_true, ← hsem]
    constructor
    · intro h
      have hpos := (h (fun _ => 1) (by intros; decide)).1
      exact ⟨(RecursorFreeVectorProof.positive_flag index mode a b).mpr hpos, fun ν hp => (h ν hp).2⟩
    · rintro ⟨hf,hh⟩ ν hp
      exact ⟨(RecursorFreeVectorProof.positive_flag index mode a b).mp hf, hh ν hp⟩

theorem completeVectorDecision : SemanticFiniteVectorTargets.CompleteVectorDecision := by
  intro ι index n mode k l a b ha hb
  obtain ⟨ta,hta⟩ := (SemanticFiniteScalarProof.exactSuccessClass ι index a.scalar).mpr ha
  obtain ⟨tb,htb⟩ := (SemanticFiniteScalarProof.exactSuccessClass ι index b.scalar).mpr hb
  exact vector_decision ι index n mode k l a b ta tb hta htb

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticFiniteVectorProof
