module
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionCodeCalibrationProof

private theorem instructions_step (n tag : Nat) (ht : tag < 5) :
    ExpressionCode.instructions (5*n+tag) =
      if tag = 0 then [(0,n)]
      else if tag = 1 then [(1,n)]
      else if tag = 2 then
        ExpressionCode.instructions n.unpair.1 ++
          ExpressionCode.instructions n.unpair.2 ++ [(2,0)]
      else if tag = 3 then ExpressionCode.instructions n.unpair.2 ++ [(3,n.unpair.1)]
      else ExpressionCode.instructions n.unpair.2 ++ [(4,n.unpair.1)] := by
  have hm : (5*n+tag)%5 = tag := by omega
  have hd : (5*n+tag)/5 = n := by omega
  rw [ExpressionCode.instructions, hm, hd]

theorem instructions_calibration (t : Expr) :
    ExpressionCode.instructions t.encode = instructions t := by
  induction t with
  | numeral n =>
      simpa [Expr.encode, instructions] using instructions_step n 0 (by decide)
  | «variable» i =>
      simpa [Expr.encode, instructions] using instructions_step i 1 (by decide)
  | add a b ha hb =>
      simpa [Expr.encode, instructions, Nat.unpair_pair, ha, hb] using
        instructions_step (Nat.pair a.encode b.encode) 2 (by decide)
  | scale k a ha =>
      simpa [Expr.encode, instructions, Nat.unpair_pair, ha] using
        instructions_step (Nat.pair k a.encode) 3 (by decide)
  | collapse code a ha =>
      simpa [Expr.encode, instructions, Nat.unpair_pair, ha] using
        instructions_step (Nat.pair code a.encode) 4 (by decide)

theorem instructions_length (t : Expr) : (instructions t).length = nodeCount t := by
  induction t with
  | numeral n => rfl
  | «variable» i => rfl
  | add a b ha hb => simp [instructions, nodeCount, ha, hb, Nat.add_assoc]
  | scale k a ha => simp [instructions, nodeCount, ha]
  | collapse code a ha => simp [instructions, nodeCount, ha]

theorem originalNames_append (a b : List Instruction) :
    ExpressionCode.originalNames (a++b) =
      ExpressionCode.originalNames a ++ ExpressionCode.originalNames b := by
  simp only [ExpressionCode.originalNames, List.filter_append, List.map_append]

theorem headNames_append (a b : List Instruction) :
    ExpressionCode.headNames (a++b) =
      ExpressionCode.headNames a ++ ExpressionCode.headNames b := by
  simp only [ExpressionCode.headNames, List.filter_append, List.map_append]

theorem instructions_originalNames (t : Expr) :
    ExpressionCode.originalNames (instructions t) = t.variables := by
  induction t with
  | numeral n => rfl
  | «variable» i => rfl
  | add a b ha hb =>
      rw [instructions, originalNames_append, originalNames_append, ha, hb]
      simp [ExpressionCode.originalNames, Expr.variables]
  | scale k a ha =>
      rw [instructions, originalNames_append, ha]
      simp [ExpressionCode.originalNames, Expr.variables]
  | collapse code a ha =>
      rw [instructions, originalNames_append, ha]
      simp [ExpressionCode.originalNames, Expr.variables]

theorem instructions_headNames (t : Expr) :
    ExpressionCode.headNames (instructions t) = t.heads := by
  induction t with
  | numeral n => rfl
  | «variable» i => rfl
  | add a b ha hb =>
      rw [instructions, headNames_append, headNames_append, ha, hb]
      simp [ExpressionCode.headNames, Expr.heads]
  | scale k a ha =>
      rw [instructions, headNames_append, ha]
      simp [ExpressionCode.headNames, Expr.heads]
  | collapse code a ha =>
      rw [instructions, headNames_append, ha]
      simp [ExpressionCode.headNames, Expr.heads]

theorem instructionCodeCalibration : ExpressionTargets.InstructionCodeCalibration :=
  fun t => ⟨instructions_calibration t, instructions_length t,
    instructions_originalNames t, instructions_headNames t⟩

private theorem output_add (start : Nat) (a b : Expr) :
    output start (.add a b) = start+nodeCount a+nodeCount b := by
  simp only [output, nodeCount]
  omega

private theorem output_scale (start k : Nat) (a : Expr) :
    output start (.scale k a) = start+nodeCount a := by
  simp only [output, nodeCount]
  omega

private theorem output_collapse (start code : Nat) (a : Expr) :
    output start (.collapse code a) = start+nodeCount a := by
  simp only [output, nodeCount]
  omega

theorem run_append (a b : List Instruction) (s : ExpressionCode.State) :
    ExpressionCode.run (a++b) s = ExpressionCode.run b (ExpressionCode.run a s) :=
  List.foldl_append

private theorem run_numeral (start n : Nat) (stack : List Nat) (prior : List Row) :
    ExpressionCode.run [(0,n)] (start,stack,prior) =
      (start+1,start::stack,prior++[numeralRow start n]) := rfl

private theorem run_variable (start i : Nat) (stack : List Nat) (prior : List Row) :
    ExpressionCode.run [(1,i)] (start,stack,prior) =
      (start+1,start::stack,prior++[variableRow start i]) := rfl

private theorem run_addition (start x y : Nat) (stack : List Nat) (prior : List Row) :
    ExpressionCode.run [(2,0)] (start,y::x::stack,prior) =
      (start+1,start::stack,prior++[additionRow start x y]) := rfl

private theorem run_scale (start k x : Nat) (stack : List Nat) (prior : List Row) :
    ExpressionCode.run [(3,k)] (start,x::stack,prior) =
      (start+1,start::stack,prior++[scaleRow start k x]) := rfl

private theorem run_collapse (start code x : Nat) (stack : List Nat) (prior : List Row) :
    ExpressionCode.run [(4,code)] (start,x::stack,prior) =
      (start+1,start::stack,prior++[headEquation code x start]) := rfl

/-- The literal postfix machine appends the exact source equations and
preserves every prior stack entry, without evaluating a collapse function. -/
theorem rowMachineCalibration : ExpressionTargets.RowMachineCalibration := by
  intro t
  induction t with
  | numeral n =>
      intro start stack prior
      rw [instructions, run_numeral]
      simp only [nodeCount, output, Nat.add_sub_cancel, rows]
  | «variable» i =>
      intro start stack prior
      rw [instructions, run_variable]
      simp only [nodeCount, output, Nat.add_sub_cancel, rows]
  | add a b ha hb =>
      intro start stack prior
      rw [instructions, run_append, run_append, ha, hb, run_addition]
      simp only [nodeCount, rows, output_add, Nat.add_assoc, List.append_assoc]
  | scale k a ha =>
      intro start stack prior
      rw [instructions, run_append, ha, run_scale]
      simp only [nodeCount, rows, output_scale, Nat.add_assoc, List.append_assoc]
  | collapse code a ha =>
      intro start stack prior
      rw [instructions, run_append, ha, run_collapse]
      simp only [nodeCount, rows, output_collapse, Nat.add_assoc, List.append_assoc]

theorem literalGraphCompiler : ExpressionTargets.LiteralGraphCompiler := by
  intro t resultName
  simp only [ExpressionCode.package, instructions_calibration, ExpressionCode.start,
    instructions_originalNames, instructions_headNames, instructions_length]
  change (familyDegree t.heads, names (freshStart t resultName) (nodeCount t),
    (ExpressionCode.run (instructions t) (freshStart t resultName,[],[])).2.2 ++
      [variableRow resultName
        ((ExpressionCode.run (instructions t) (freshStart t resultName,[],[])).1-1)]) =
    expressionPackage t resultName
  rw [rowMachineCalibration t (freshStart t resultName) [] []]
  rfl

end LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionCodeCalibrationProof
