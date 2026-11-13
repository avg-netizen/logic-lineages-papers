module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceDecisionCodeTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.BooleanGraphCodePredicateProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundProjectionCodeStatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceDecisionProof
open SourceDecision NonlinearProjectionCompletion BooleanGraphCodeProof
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair

def embeddingChildren (code : Nat) : List Nat :=
  if code % 4 = 0 ∨ code % 4 = 1 then []
  else if code % 4 = 2 then [(code / 4).unpair.1, (code / 4).unpair.2]
  else [code / 4]
def embeddingAssemble (code : Nat) (values : List Nat) : Nat :=
  if code % 4 = 0 then 10 * (code / 4)
  else if code % 4 = 1 then 10 * (code / 4) + 1
  else if code % 4 = 2 then WindowCode.add (values.getD 0 0) (values.getD 1 0)
  else WindowCode.phi (values.getD 0 0)

theorem embeddingChildren_primitive : Primrec embeddingChildren :=
  Primrec.ite ((tag_is 4 0).or (tag_is 4 1)) (Primrec.const [])
    (Primrec.ite (tag_is 4 2)
      (Primrec.list_cons.comp (left_primitive 4)
        (Primrec.list_cons.comp (right_primitive 4) (Primrec.const [])))
      (Primrec.list_cons.comp (quotient_primitive 4) (Primrec.const [])))
theorem embeddingAssemble_primitive : Primrec₂ embeddingAssemble := by
  let A := Nat × List Nat
  have h0 : Primrec (fun p : A => p.2.getD 0 0) :=
    (Primrec.list_getD (0 : Nat)).comp Primrec.snd (Primrec.const 0)
  have h1 : Primrec (fun p : A => p.2.getD 1 0) :=
    (Primrec.list_getD (0 : Nat)).comp Primrec.snd (Primrec.const 1)
  exact Primrec.ite ((tag_is 4 0).comp Primrec.fst)
    ((unary_primitive 10 0).comp ((quotient_primitive 4).comp Primrec.fst))
    (Primrec.ite ((tag_is 4 1).comp Primrec.fst)
      ((unary_primitive 10 1).comp ((quotient_primitive 4).comp Primrec.fst))
      (Primrec.ite ((tag_is 4 2).comp Primrec.fst)
        ((binary_primitive 10 2).comp h0 h1) ((unary_primitive 10 6).comp h0)))
theorem embeddingChildren_decreasing : ∀ code child : Nat,
    child ∈ embeddingChildren code → child < code := by
  intro code child h
  by_cases hleaf : code % 4 = 0 ∨ code % 4 = 1
  · simp [embeddingChildren, hleaf] at h
  have hp : 0 < code := by omega
  have hd : code / 4 < code := Nat.div_lt_self hp (by decide)
  have hl := Nat.unpair_left_le (code / 4)
  have hr := Nat.unpair_right_le (code / 4)
  unfold embeddingChildren at h
  split_ifs at h <;> simp_all only [List.mem_cons, List.not_mem_nil, or_false]
  all_goals omega
theorem embedding_equation (code : Nat) : embedTerm code =
    embeddingAssemble code ((embeddingChildren code).map embedTerm) := by
  rw [embedTerm]
  split_ifs <;> simp_all [embeddingChildren, embeddingAssemble, WindowCode.add, WindowCode.phi]
theorem embedTerm_computable : Computable embedTerm := by
  classical
  exact (FiniteGraph.Proof.exactDecreasingGraph Nat Nat embeddingChildren embeddingAssemble id
    embeddingChildren_primitive.to_comp embeddingAssemble_primitive.to_comp Computable.id
    embedTerm embeddingChildren_decreasing embedding_equation).2

theorem binder_computable : Computable₂ binder := by
  have hi : Computable (fun p : Nat × Nat => [p.1]) :=
    Primrec.list_cons.to_comp.comp Computable.fst (Computable.const [])
  exact WholeBoundProjectionCodeProof.actualJointProgram.comp
    (Primrec.list_cons.to_comp.comp Computable.fst
      (BooleanGraphCodeProof.allocated_computable.comp hi Computable.snd))
    (BooleanGraphCodeProof.compile_computable.comp hi Computable.snd)

def sourceChildren (code : Nat) : List Nat :=
  if code % 5 = 0 ∨ code % 5 = 1 then []
  else if code % 5 = 2 then [code / 5]
  else if code % 5 = 3 then [(code / 5).unpair.1, (code / 5).unpair.2]
  else [(code / 5).unpair.2]
def sourceAssemble (code : Nat) (values : List Nat) : Nat :=
  if code % 5 = 0 then (8 * Nat.pair (embedTerm (code / 5).unpair.1) (embedTerm (code / 5).unpair.2) + 2)
  else if code % 5 = 1 then WindowCode.less
    (embedTerm (code / 5).unpair.1) (embedTerm (code / 5).unpair.2)
  else if code % 5 = 2 then WindowCode.negative (values.getD 0 0)
  else if code % 5 = 3 then WindowCode.conjunction (values.getD 0 0) (values.getD 1 0)
  else binder (code / 5).unpair.1 (values.getD 0 0)

theorem sourceChildren_primitive : Primrec sourceChildren :=
  Primrec.ite ((tag_is 5 0).or (tag_is 5 1)) (Primrec.const [])
    (Primrec.ite (tag_is 5 2)
      (Primrec.list_cons.comp (quotient_primitive 5) (Primrec.const []))
      (Primrec.ite (tag_is 5 3)
        (Primrec.list_cons.comp (left_primitive 5)
          (Primrec.list_cons.comp (right_primitive 5) (Primrec.const [])))
        (Primrec.list_cons.comp (right_primitive 5) (Primrec.const []))))
theorem sourceAssemble_computable : Computable₂ sourceAssemble := by
  let A := Nat × List Nat
  have h0 : Computable (fun p : A => p.2.getD 0 0) :=
    (Primrec.list_getD (0 : Nat)).to_comp.comp Computable.snd (Computable.const 0)
  have h1 : Computable (fun p : A => p.2.getD 1 0) :=
    (Primrec.list_getD (0 : Nat)).to_comp.comp Computable.snd (Computable.const 1)
  have hl : Computable (fun p : A => (p.1 / 5).unpair.1) := (left_primitive 5).to_comp.comp Computable.fst
  have hr : Computable (fun p : A => (p.1 / 5).unpair.2) := (right_primitive 5).to_comp.comp Computable.fst
  exact ComputableMapAtomsProof.computable_ite ((tag_is 5 0).comp Primrec.fst)
    ((binary_primitive 8 2).to_comp.comp (embedTerm_computable.comp hl) (embedTerm_computable.comp hr))
    (ComputableMapAtomsProof.computable_ite ((tag_is 5 1).comp Primrec.fst)
      ((binary_primitive 8 3).to_comp.comp (embedTerm_computable.comp hl) (embedTerm_computable.comp hr))
      (ComputableMapAtomsProof.computable_ite ((tag_is 5 2).comp Primrec.fst)
        ((unary_primitive 8 5).to_comp.comp h0)
        (ComputableMapAtomsProof.computable_ite ((tag_is 5 3).comp Primrec.fst)
          ((binary_primitive 8 6).to_comp.comp h0 h1) (binder_computable.comp hl h0))))
theorem sourceChildren_decreasing : ∀ code child : Nat,
    child ∈ sourceChildren code → child < code := by
  intro code child h
  by_cases hleaf : code % 5 = 0 ∨ code % 5 = 1
  · simp [sourceChildren, hleaf] at h
  have hp : 0 < code := by omega
  have hd : code / 5 < code := Nat.div_lt_self hp (by decide)
  have hl := Nat.unpair_left_le (code / 5)
  have hr := Nat.unpair_right_le (code / 5)
  unfold sourceChildren at h
  split_ifs at h <;> simp_all only [List.mem_cons, List.not_mem_nil, or_false]
  all_goals omega
theorem source_equation (code : Nat) : eliminate code =
    sourceAssemble code ((sourceChildren code).map eliminate) := by
  rw [eliminate]
  split_ifs <;> simp_all [sourceChildren, sourceAssemble]
theorem eliminate_computable : Computable eliminate := by
  classical
  exact (FiniteGraph.Proof.exactDecreasingGraph Nat Nat sourceChildren sourceAssemble id
    sourceChildren_primitive.to_comp sourceAssemble_computable Computable.id
    eliminate sourceChildren_decreasing source_equation).2

theorem actualCompilerPrograms : SourceDecisionTargets.ActualCompilerPrograms :=
  ⟨embedTerm_computable, binder_computable, eliminate_computable⟩
#print axioms embeddingChildren_primitive
#print axioms embeddingAssemble_primitive
#print axioms embeddingChildren_decreasing
#print axioms embedding_equation
#print axioms embedTerm_computable
#print axioms binder_computable
#print axioms sourceChildren_primitive
#print axioms sourceAssemble_computable
#print axioms sourceChildren_decreasing
#print axioms source_equation
#print axioms eliminate_computable
#print axioms actualCompilerPrograms
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceDecisionProof
