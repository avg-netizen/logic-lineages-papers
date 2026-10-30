module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowAtomicRegistry
public import LogicLineages.ComputabilityKnowledge.GorbowRegistryDispatchProof
public import LogicLineages.ComputabilityKnowledge.GorbowArithmeticEvaluationProof
public import LogicLineages.ComputabilityKnowledge.GorbowSortedSimultaneousCodeProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowAtomicRegistryProof
open GorbowSyntax GorbowStandardInstances GorbowSortedSyntaxCode GorbowRegistryTuple GorbowRegistryDecoder
open GorbowRegistryDispatch GorbowAtomicRegistry

private theorem headerAt (arity tag : Nat) (args : List Nat) : decodeHeader (header arity tag args)=some (arity,tag,args) :=
  (GorbowRegistryDecoderProof.headerExact _ _ _ _).mpr rfl
private theorem tupleAt (codes : List Nat) : decodeTuple (tuple codes)=some codes :=
  (GorbowRegistryDecoderProof.tupleExact _ _).mpr rfl

theorem tupleExact : Comparators.GorbowAtomicRegistry.TupleExact := by
  intro n code packed out
  constructor
  · intro h
    cases hd : decodeTuple packed with
    | none => simp [tupleSubstitute,hd] at h
    | some codes =>
      exact ⟨codes,((GorbowRegistryDecoderProof.tupleExact packed codes).mp hd).symm,
        by simpa [tupleSubstitute,hd] using h⟩
  · rintro ⟨codes,rfl,h⟩
    simpa [tupleSubstitute,tupleAt] using h

theorem newDispatch : Comparators.GorbowAtomicRegistry.NewDispatch := by
  intro a b c
  simp [functionProgram,headerAt]

theorem originalDispatch : Comparators.GorbowAtomicRegistry.OriginalDispatch := by
  constructor
  · exact GorbowRegistryDispatchProof.originalGround.1
  · intro a b c
    simpa [ground,functionProgram,headerAt] using GorbowSortedRegistryProof.functionDispatch a b c

theorem actualCalibration : Comparators.GorbowAtomicRegistry.ActualCalibration := by
  constructor
  · intro t ht I
    rw [(newDispatch (termCode t) 0 0).1]
    have hv := (GorbowArithmeticEvaluationProof.exactSortedOutput (termCode t) (t.realize I Fin.elim0) I).mpr ⟨t,rfl,ht,rfl⟩
    rw [hv]
    rfl
  · intro n φ σ
    rw [(newDispatch n (formulaCode φ) (tuple (List.ofFn (fun i => termCode (σ i))))).2]
    have hv := (tupleExact n (formulaCode φ) _ _).mpr
      ⟨List.ofFn (fun i => termCode (σ i)),rfl,GorbowSortedSimultaneousCodeProof.actualCalibration n φ σ⟩
    rw [hv]
    rfl

theorem fallback : Comparators.GorbowAtomicRegistry.Fallback := by
  constructor
  · intro code h; simp [functionProgram,h]
  · intro arity tag args h1 h2; simp [functionProgram,headerAt,h1,h2]

private theorem pr_tupleBody : Primrec (fun p : (Nat × Nat × Nat) × List Nat =>
    GorbowSortedSimultaneousCode.substituteNumber p.1.1 p.1.2.1 p.2) :=
  GorbowSortedSimultaneousCodeProof.uniformPrograms.2.2.comp
    ((Primrec.fst.comp Primrec.fst).pair ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd))
private theorem pr_tuple : Primrec (fun p : Nat × Nat × Nat => tupleSubstitute p.1 p.2.1 p.2.2) :=
  Primrec.option_bind (GorbowRegistryDecoderProof.uniformPrograms.2.2.2.1.comp (Primrec.snd.comp Primrec.snd)) pr_tupleBody.to₂
private abbrev Header := Nat × Nat × List Nat
private theorem pr_args : Primrec (fun p : Nat × Header => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
private theorem pr_arg (i : Nat) : Primrec (fun p : Nat × Header => p.2.2.2.getD i 0) :=
  (Primrec.list_getD 0).comp pr_args (Primrec.const i)
private theorem pr_shape (arity tag count : Nat) : PrimrecPred (fun p : Nat × Header => p.2.1=arity ∧ p.2.2.1=tag ∧ p.2.2.2.length=count) :=
  (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const arity)).and
    ((Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const tag)).and
      (Primrec.eq.comp (Primrec.list_length.comp pr_args) (Primrec.const count)))
private theorem pr_body : Primrec (fun p : Nat × Header =>
    if p.2.1=1 ∧ p.2.2.1=1 ∧ p.2.2.2.length=1 then
      (GorbowArithmeticEvaluation.sortedValue (p.2.2.2.getD 0 0)).getD 0
    else if p.2.1=3 ∧ p.2.2.1=1 ∧ p.2.2.2.length=3 then
      (tupleSubstitute (p.2.2.2.getD 0 0) (p.2.2.2.getD 1 0) (p.2.2.2.getD 2 0)).getD 0
    else GorbowSortedRegistry.functionProgram p.1) :=
  Primrec.ite (pr_shape 1 1 1)
    (Primrec.option_getD.comp (GorbowArithmeticEvaluationProof.uniformPrograms.2.2.2.comp (pr_arg 0)) (Primrec.const 0))
    (Primrec.ite (pr_shape 3 1 3)
      (Primrec.option_getD.comp (pr_tuple.comp ((pr_arg 0).pair ((pr_arg 1).pair (pr_arg 2)))) (Primrec.const 0))
      (GorbowSortedRegistryProof.uniformPrograms.2.comp Primrec.fst))
private theorem pr_function : Primrec functionProgram := by
  have h := Primrec.option_casesOn GorbowRegistryDecoderProof.uniformPrograms.2.2.2.2
    GorbowSortedRegistryProof.uniformPrograms.2 pr_body.to₂
  exact h.of_eq (fun code => by cases hd : decodeHeader code <;> simp [functionProgram,hd])

theorem uniformPrograms : Comparators.GorbowAtomicRegistry.UniformPrograms := ⟨pr_tuple,pr_function⟩
theorem gorbowAtomicRegistry : Comparators.GorbowAtomicRegistry.Target :=
  ⟨tupleExact,newDispatch,originalDispatch,actualCalibration,fallback,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowAtomicRegistryProof
