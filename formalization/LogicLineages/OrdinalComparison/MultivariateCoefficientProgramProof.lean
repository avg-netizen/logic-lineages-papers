module
public import LogicLineages.OrdinalComparison.MultivariateNormalizeCodeTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.MultivariateNormalizeCode

theorem coefficient_code (xs : List Nat) : multivariateCoefficientCode xs=Encodable.encode xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change Nat.pair x (multivariateCoefficientCode xs)+1=Nat.succ (Nat.pair x (Encodable.encode xs))
    rw [ih]

private theorem vector_length (a b : List Nat) :
    (multivariateCoefficientAdd a b).length=max a.length b.length := by
  induction a generalizing b with
  | nil => simp [multivariateCoefficientAdd]
  | cons x xs ih =>
    cases b with
    | nil => simp [multivariateCoefficientAdd]
    | cons y ys =>
      simp only [multivariateCoefficientAdd,List.length_cons,ih]
      omega

private theorem vector_getD (a b : List Nat) (i : Nat) :
    (multivariateCoefficientAdd a b).getD i 0=a.getD i 0+b.getD i 0 := by
  induction a generalizing b i with
  | nil => simp [multivariateCoefficientAdd]
  | cons x xs ih =>
    cases b with
    | nil => simp [multivariateCoefficientAdd]
    | cons y ys =>
      cases i with
      | zero => rfl
      | succ i => simpa only [multivariateCoefficientAdd,List.getD_cons_succ] using ih ys i

private theorem vector_range (a b : List Nat) :
    multivariateCoefficientAdd a b=(List.range (max a.length b.length)).map
      (fun i => a.getD i 0+b.getD i 0) := by
  apply List.ext_getElem
  · simp only [vector_length,List.length_map,List.length_range]
  · intro i hi hj
    have h := vector_getD a b i
    simpa [List.getD_eq_getElem?_getD,hi] using h

private theorem coefficient_add_primitive : Primrec₂ multivariateCoefficientAdd := by
  have hr : Primrec (fun p : List Nat × List Nat => List.range (max p.1.length p.2.length)) :=
    Primrec.list_range.comp (Primrec.nat_max.comp (Primrec.list_length.comp Primrec.fst)
      (Primrec.list_length.comp Primrec.snd))
  have ha : Primrec (fun p : (List Nat × List Nat) × Nat => p.1.1) := Primrec.fst.comp Primrec.fst
  have hb : Primrec (fun p : (List Nat × List Nat) × Nat => p.1.2) := Primrec.snd.comp Primrec.fst
  have hg : Primrec₂ (fun p : List Nat × List Nat => fun i : Nat => p.1.getD i 0+p.2.getD i 0) :=
    Primrec.nat_add.comp ((Primrec.list_getD 0).comp ha Primrec.snd)
      ((Primrec.list_getD 0).comp hb Primrec.snd)
  exact (Primrec.list_map hr hg).of_eq (fun p => (vector_range p.1 p.2).symm)

private theorem variable_coefficients_primitive : Primrec₂ multivariateVariableCoefficients := by
  have hz : Primrec (fun p : Nat × Nat => List.replicate p.1 0) :=
    (Primrec.list_map (Primrec.list_range.comp Primrec.fst) (Primrec.const (0 : Nat)).to₂).of_eq
      (fun p => by simp)
  have hs : Primrec (fun p : Nat × Nat => [p.2]) :=
    Primrec.list_cons.comp Primrec.snd (Primrec.const [])
  exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
    (Primrec.const []) (Primrec.list_append.comp hz hs)

private theorem coefficient_code_primitive : Primrec multivariateCoefficientCode :=
  Primrec.encode.of_eq (fun xs => (coefficient_code xs).symm)

theorem coefficients : Targets.MultivariateCoefficientPrograms := by
  refine ⟨?_,?_,?_,?_⟩
  · have ha : Primrec (fun p : Nat × Nat => (Encodable.decode (α := List Nat) p.1).getD []) :=
      Primrec.option_getD.comp (Primrec.decode.comp Primrec.fst) (Primrec.const [])
    have hb : Primrec (fun p : Nat × Nat => (Encodable.decode (α := List Nat) p.2).getD []) :=
      Primrec.option_getD.comp (Primrec.decode.comp Primrec.snd) (Primrec.const [])
    exact coefficient_code_primitive.comp (coefficient_add_primitive.comp ha hb)
  · exact coefficient_code_primitive.comp variable_coefficients_primitive
  · intro a b
    simp only [encodedMultivariateCoefficientAdd,coefficient_code,Encodable.encodek,Option.getD_some]
  · intro i a
    rfl

end LogicLineages.OrdinalComparison.MultivariateNormalizeCode
