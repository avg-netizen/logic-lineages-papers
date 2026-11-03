module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedRawCompilerTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxFormulaProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedGuardDescentProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCodePrimitiveProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedRawCompiler.Proof

attribute [local irreducible] Nat.sqrt Nat.unpair rawNormCode
  BalancedBoxFormula.formulaCode BalancedGuardDescent.sourceChildren
  BalancedGuardDescent.sourceAssemble

private theorem baseCode_primitive :
    Primrec (fun p : Nat × Nat × Int => baseCode p.1 p.2.1 p.2.2) := by
  let D := Nat × Nat × Int
  have he : Primrec (fun p : D => p.1) := Primrec.fst
  have hf : Primrec (fun p : D => p.2.1) := Primrec.fst.comp Primrec.snd
  have hd : Primrec (fun p : D => p.2.2) := Primrec.snd.comp Primrec.snd
  have heq : Primrec (fun p : D => [(2, p.1, p.2.1)]) :=
    Primrec.list_cons.comp ((Primrec.const 2).pair (he.pair hf)) (Primrec.const [])
  have hlt : Primrec (fun p : D => [(3, p.1, p.2.1)]) :=
    Primrec.list_cons.comp ((Primrec.const 3).pair (he.pair hf)) (Primrec.const [])
  have hgt : Primrec (fun p : D => [(3, p.2.1, p.1)]) :=
    Primrec.list_cons.comp ((Primrec.const 3).pair (hf.pair he)) (Primrec.const [])
  exact Primrec.ite (Primrec.eq.comp hd (Primrec.const 0)) heq
    (Primrec.ite (Primrec.eq.comp hd (Primrec.const (-1))) hlt
      (Primrec.ite (Primrec.eq.comp hd (Primrec.const 1)) hgt
        (Primrec.const [(0, 0, 0)])))

attribute [local irreducible] baseCode

private theorem input_shape : Computable (fun a : Input => a.1) := Computable.fst
private theorem input_tail1 : Computable (fun a : Input => a.2) := Computable.snd
private theorem input_certificate : Computable (fun a : Input => a.2.1) :=
  Computable.fst.comp input_tail1
private theorem input_tail2 : Computable (fun a : Input => a.2.2) :=
  Computable.snd.comp input_tail1
private theorem input_left : Computable (fun a : Input => a.2.2.1) :=
  Computable.fst.comp input_tail2
private theorem input_tail3 : Computable (fun a : Input => a.2.2.2) :=
  Computable.snd.comp input_tail2
private theorem input_right : Computable (fun a : Input => a.2.2.2.1) :=
  Computable.fst.comp input_tail3
private theorem input_desired : Computable (fun a : Input => a.2.2.2.2) :=
  Computable.snd.comp input_tail3
private theorem input_head : Computable (fun a : Input => a.1.getD 0 0) :=
  (Primrec.list_getD (0 : Nat)).to_comp.comp input_shape (Computable.const 0)
private theorem input_shape_tail : Computable (fun a : Input => a.1.tail) :=
  Primrec.list_tail.to_comp.comp input_shape
private theorem input_empty : Computable (fun a : Input => decide (a.1 = [])) :=
  Primrec.eq.decide.to_comp.comp input_shape (Computable.const [])

private theorem upper_arguments : Computable (fun a : Input =>
    (a.1.getD 0 0, a.1.tail, a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2)) :=
  input_head.pair (input_shape_tail.pair (input_certificate.pair
    (input_left.pair (input_right.pair input_desired))))

private theorem sourceChildren_computable :
    Computable (fun p : Nat × List Nat × Nat × Nat × Nat × Int =>
      BalancedGuardDescent.sourceChildren p.1 p.2.1 p.2.2.1 p.2.2.2.1
        p.2.2.2.2.1 p.2.2.2.2.2) := by
  rcases BalancedGuardDescent.Proof.uniformPrimitiveRecursive with
    ⟨_, _, _, _, _, h, _, _⟩
  exact h.to_comp

private theorem children_computable : Computable children := by
  apply (Computable.cond input_empty (Computable.const ([] : List Input))
    (sourceChildren_computable.comp upper_arguments)).of_eq
  intro a
  cases h : a.1 <;> simp [children, h]

private theorem sourceAssemble_computable :
    Computable (fun p : Nat × Nat × Nat × Int × List Code =>
      BalancedGuardDescent.sourceAssemble p.1 p.2.1 p.2.2.1 p.2.2.2.1
        p.2.2.2.2) := by
  rcases BalancedGuardDescent.Proof.uniformPrimitiveRecursive with
    ⟨_, _, _, _, _, _, h, _⟩
  exact h.to_comp

private abbrev Assembly := Input × List Code

private theorem assembly_base : Computable (fun p : Assembly =>
    baseCode p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2) :=
  baseCode_primitive.to_comp.comp
    ((input_left.comp Computable.fst).pair
      ((input_right.comp Computable.fst).pair (input_desired.comp Computable.fst)))

private theorem assembly_box : Computable (fun p : Assembly =>
    BalancedBoxFormula.formulaCode (p.1.1.getD 0 0) p.1.1.tail p.1.2.1
      p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2) :=
  BalancedBoxFormula.Proof.allCodeComputation.comp
    (upper_arguments.comp Computable.fst)

private theorem assembly_guards : Computable (fun p : Assembly =>
    BalancedGuardDescent.sourceAssemble (p.1.1.getD 0 0) p.1.2.2.1
      p.1.2.2.2.1 p.1.2.2.2.2 p.2) :=
  sourceAssemble_computable.comp
    ((input_head.comp Computable.fst).pair
      ((input_left.comp Computable.fst).pair
        ((input_right.comp Computable.fst).pair
          ((input_desired.comp Computable.fst).pair Computable.snd))))

private theorem assemble_computable : Computable₂ assemble := by
  apply (Computable.cond (input_empty.comp Computable.fst) assembly_base
    (CommonHeadCode.Program.disjunction_primitive.to_comp.comp
      assembly_box assembly_guards)).of_eq
  intro p
  cases h : p.1.1 <;> simp [assemble, h]

private theorem measure_computable : Computable measure :=
  Primrec.list_length.to_comp.comp input_shape

/-- The actual raw interfaces retain every source payload and all default
behavior. Only the genuine empty source shape selects the literal BASE leaf;
the finite-box branch is computable, without a primitive-recursion claim. -/
theorem numericalInterfaces : Targets.NumericalInterfaces :=
  ⟨baseCode_primitive.to_comp, children_computable, assemble_computable,
    measure_computable⟩

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedRawCompiler.Proof
