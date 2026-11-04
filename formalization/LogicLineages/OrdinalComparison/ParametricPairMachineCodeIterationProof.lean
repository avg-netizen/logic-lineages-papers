module
public import LogicLineages.OrdinalComparison.ParametricPairMachineCodeKernelProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPairMachineCode.Proof
open ParametricPairWorklist

private theorem initial_primitive : Primrec initial :=
  (Primrec.list_cons.comp Primrec.sumInl (Primrec.const [])).pair (Primrec.const [])

private theorem rec_eq_iterate (f : State → State) (s : State) (n : Nat) :
    Nat.rec s (fun _ r => f r) n = f^[n] s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change f (Nat.rec s (fun _ r => f r) n) = f^[n+1] s
    rw [Function.iterate_succ_apply',ih]

/-- Every bounded indexed machine operation is primitive recursive. -/
theorem indexedPrimitiveRecursive : Targets.IndexedPrimitiveRecursive := by
  intro H hH
  have hquery := kernelPrimitiveRecursive.2.1
  have hkernel := kernelPrimitiveRecursive.2.2.1
  have hresult := kernelPrimitiveRecursive.2.2.2
  have hs : Primrec (fun p : Nat × State => indexedStep H p.1 p.2) :=
    hkernel.comp ((hH.comp (Primrec.fst.pair (hquery.comp Primrec.snd))).pair Primrec.snd)
  have hb : Primrec (fun p : ((Nat × Nat) × State) × (Nat × State) =>
      indexedStep H p.1.1.1 p.2.2) :=
    hs.comp ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
      (Primrec.snd.comp Primrec.snd))
  have hr : Primrec (fun p : (Nat × Nat) × State =>
      indexedRun H p.1.1 p.1.2 p.2) := by
    apply (Primrec.nat_rec' (Primrec.snd.comp Primrec.fst) Primrec.snd hb.to₂).of_eq
    intro p
    exact rec_eq_iterate (indexedStep H p.1.1) p.2 p.1.2
  refine ⟨hs,hr,?_⟩
  exact hresult.comp (hr.comp
    (((Primrec.fst.comp Primrec.fst).pair Primrec.snd).pair
      (initial_primitive.comp (Primrec.snd.comp Primrec.fst))))

attribute [local irreducible] childrenBudget query stepBudget indexedStep indexedRun initial result
attribute [local irreducible] Nat.unpair Nat.sqrt Computable Partrec

private theorem query_computable : Computable query :=
  kernelPrimitiveRecursive.2.1.to_comp

private theorem budget_computable :
    Computable (fun p : Nat × State => stepBudget p.1 p.2) :=
  kernelPrimitiveRecursive.2.2.1.to_comp

private theorem result_computable : Computable result :=
  kernelPrimitiveRecursive.2.2.2.to_comp

private theorem indexed_step_computable (H : Nat × Nat → Nat) (hH : Computable H) :
    Computable (fun p : Nat × State => indexedStep H p.1 p.2) := by
  unfold indexedStep
  exact budget_computable.comp
    ((hH.comp (Computable.fst.pair (query_computable.comp Computable.snd))).pair Computable.snd)

private theorem indexed_body_computable (H : Nat × Nat → Nat) (hH : Computable H) :
    Computable (fun p : ((Nat × Nat) × State) × (Nat × State) =>
      indexedStep H p.1.1.1 p.2.2) :=
  (indexed_step_computable H hH).comp
    ((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
      (Computable.snd.comp Computable.snd))

private theorem indexed_run_computable (H : Nat × Nat → Nat) (hH : Computable H) :
    Computable (fun p : (Nat × Nat) × State => indexedRun H p.1.1 p.1.2 p.2) := by
  apply (Computable.nat_rec (Computable.snd.comp Computable.fst) Computable.snd
    (indexed_body_computable H hH).to₂).of_eq
  intro p
  simpa only [indexedRun] using rec_eq_iterate (indexedStep H p.1.1) p.2 p.1.2

/-- The same bounded iterations are computable for every computable indexed budget. -/
theorem indexedComputable : Targets.IndexedComputable := by
  intro H hH
  refine ⟨indexed_step_computable H hH,indexed_run_computable H hH,?_⟩
  unfold indexedEvaluate
  exact result_computable.comp ((indexed_run_computable H hH).comp
    (((Computable.fst.comp Computable.fst).pair Computable.snd).pair
      (initial_primitive.to_comp.comp (Computable.snd.comp Computable.fst))))
end LogicLineages.OrdinalComparison.Source.ParametricPairMachineCode.Proof
