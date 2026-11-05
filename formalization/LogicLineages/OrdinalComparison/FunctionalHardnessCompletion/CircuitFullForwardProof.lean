module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitFullAllocationProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitFullRowsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitFull.Proof
open Polynomial CircuitLinear Narendran
open LogicLineages.ComputabilityKnowledge.CircuitReduction

private theorem signed_natCast (n : Nat) : signed (n : NPolynomial)=C (n : Int) := by
  simp [signed]

private noncomputable def squareWitness (u : Nat) : Fin 4 → NPolynomial :=
  Classical.choose ((Narendran.Proof.exactSquareGadget u (triangularNat u)).mpr
    (CircuitLinear.Proof.triangular_identity u))

private theorem squareWitness_spec (u : Nat) :
    SquareGadget u (triangularNat u) (squareWitness u) :=
  Classical.choose_spec ((Narendran.Proof.exactSquareGadget u (triangularNat u)).mpr
    (CircuitLinear.Proof.triangular_identity u))

private def scalarValue (v : Nat → Nat) (gate : Gate) (j : Fin 4) : Nat :=
  match gate with
  | .mul x y => match j.val with
    | 0 => v x+v y
    | 1 => triangularNat (v x)
    | 2 => triangularNat (v y)
    | _ => triangularNat (v x+v y)
  | _ => 0

private def squareInput (v : Nat → Nat) (gate : Gate) (k : Fin 3) : Nat :=
  match gate with
  | .mul x y => match k.val with
    | 0 => v x
    | 1 => v y
    | _ => v x+v y
  | _ => 0

private noncomputable def initialValues (c : Circuit) (v : Nat → Nat) :
    Slot c.inputCount c.gates.length → NPolynomial
  | .wire i => C (v i.val)
  | .slack i => C (v i.val-1)
  | .scalar i j => C (scalarValue v c.gates[i.val] j)
  | .square i k j => squareWitness (squareInput v c.gates[i.val] k) j
  | .constant _ => 0

private theorem initial_scalars_constant (c : Circuit) (v : Nat → Nat)
    (j : Nat) (hj : j<scalarCount c.inputCount c.gates.length) :
    ∃ k : Nat, allocate (initialValues c v) j=C k := by
  rcases scalar_slots_cover c.inputCount c.gates.length j hj with h | h | h
  · obtain ⟨i,rfl⟩ := h
    exact ⟨v i.val,allocate_at _ _⟩
  · obtain ⟨i,rfl⟩ := h
    exact ⟨v i.val-1,allocate_at _ _⟩
  · obtain ⟨i,k,rfl⟩ := h
    exact ⟨scalarValue v c.gates[i.val] k,allocate_at _ _⟩

private noncomputable def finalValues (c : Circuit) (v : Nat → Nat)
    (V extra : NPolynomial) (w : Fin 7 → NPolynomial) :
    Slot c.inputCount c.gates.length → NPolynomial
  | .constant j => if h0 : j.val=0 then V else if h1 : j.val=1 then extra
      else w ⟨j.val-2,by omega⟩
  | s => initialValues c v s

private theorem final_wire (c : Circuit) (v : Nat → Nat) (V extra : NPolynomial)
    (w : Fin 7 → NPolynomial) (i : Nat) (hi : i<c.inputCount+c.gates.length) :
    allocate (finalValues c v V extra w) i=C (v i) := by
  exact allocate_at _ (Slot.wire ⟨i,hi⟩)

private theorem final_slack (c : Circuit) (v : Nat → Nat) (V extra : NPolynomial)
    (w : Fin 7 → NPolynomial) (i : Fin c.inputCount) :
    allocate (finalValues c v V extra w) (c.inputCount+c.gates.length+i.val)=C (v i.val-1) := by
  exact allocate_at _ (Slot.slack i)

private theorem final_scalar (c : Circuit) (v : Nat → Nat) (V extra : NPolynomial)
    (w : Fin 7 → NPolynomial) (i : Fin c.gates.length) (j : Fin 4) :
    allocate (finalValues c v V extra w)
      ((c.inputCount+c.gates.length)+c.inputCount+4*i.val+j.val)=
      C (scalarValue v c.gates[i.val] j) := by
  exact allocate_at _ (Slot.scalar i j)

private theorem final_square (c : Circuit) (v : Nat → Nat) (V extra : NPolynomial)
    (w : Fin 7 → NPolynomial) (i : Fin c.gates.length) (k : Fin 3) (j : Fin 4) :
    allocate (finalValues c v V extra w)
      (polynomialAux c.inputCount c.gates.length+12*i.val+4*k.val+j.val)=
      squareWitness (squareInput v c.gates[i.val] k) j := by
  exact allocate_at _ (Slot.square i k j)

private theorem final_prefix (c : Circuit) (v : Nat → Nat) (V extra : NPolynomial)
    (w : Fin 7 → NPolynomial) (j : Nat) (hj : j<scalarCount c.inputCount c.gates.length) :
    allocate (finalValues c v V extra w) j=allocate (initialValues c v) j := by
  rcases scalar_slots_cover c.inputCount c.gates.length j hj with h | h | h
  · obtain ⟨i,rfl⟩ := h
    rw [allocate_at,allocate_at]
    rfl
  · obtain ⟨i,rfl⟩ := h
    rw [allocate_at,allocate_at]
    rfl
  · obtain ⟨i,k,rfl⟩ := h
    rw [allocate_at,allocate_at]
    rfl

private theorem final_constant (c : Circuit) (v : Nat → Nat) (V extra : NPolynomial)
    (w : Fin 7 → NPolynomial) :
    let p := allocate (finalValues c v V extra w)
    let a := constantAux c.inputCount c.gates.length
    p a=V ∧ p (a+1)=extra ∧ ∀ j : Fin 7,p (a+2+j.val)=w j := by
  dsimp only
  have h0 := allocate_at (finalValues c v V extra w) (Slot.constant 0)
  have h1 := allocate_at (finalValues c v V extra w) (Slot.constant 1)
  refine ⟨?_,?_,?_⟩
  · simpa [slotIndex,finalValues] using h0
  · simpa [slotIndex,finalValues] using h1
  · intro j
    have hj := allocate_at (finalValues c v V extra w) (Slot.constant ⟨2+j.val,by omega⟩)
    simpa [slotIndex,finalValues,Nat.add_assoc,show 2+j.val≠0 by omega,
      show 2+j.val≠1 by omega] using hj

/-- The six constant rows are simultaneously realizable after the entire
scalar prefix has been fixed. No square witness is included in that prefix. -/
private theorem realize_constant_rows (c : Circuit) (v : Nat → Nat) :
    ∃ (V extra : NPolynomial) (w : Fin 7 → NPolynomial),
      RowsSolve (allocate (finalValues c v V extra w))
        (constantRows (scalarCount c.inputCount c.gates.length)
          (constantAux c.inputCount c.gates.length)) := by
  let q := allocate (initialValues c v)
  have hs : ∀ j : Fin (scalarCount c.inputCount c.gates.length),∃ k : Nat,q j.val=C k := by
    intro j
    exact initial_scalars_constant c v j.val j.isLt
  obtain ⟨V,extra,w,hg,he⟩ := (Narendran.Proof.exactSimultaneousConstants
    (scalarCount c.inputCount c.gates.length) (fun j => q j.val)).mpr hs
  let p := allocate (finalValues c v V extra w)
  have hconst : p (constantAux c.inputCount c.gates.length)=V ∧
      p (constantAux c.inputCount c.gates.length+1)=extra ∧
      ∀ j : Fin 7,p (constantAux c.inputCount c.gates.length+2+j.val)=w j :=
    final_constant c v V extra w
  refine ⟨V,extra,w,?_⟩
  apply (CircuitLinear.Proof.constant_rows_equations p _ _).mpr
  constructor
  · have hw : (fun j : Fin 7 => p (constantAux c.inputCount c.gates.length+2+j.val))=w :=
      funext hconst.2.2
    rw [hconst.1,hw]
    exact hg
  · have hsum : (∑ j : Fin (scalarCount c.inputCount c.gates.length),p j.val)=
        ∑ j : Fin (scalarCount c.inputCount c.gates.length),q j.val := by
      apply Finset.sum_congr rfl
      intro j _
      exact final_prefix c v V extra w j.val j.isLt
    rw [hsum,hconst.1,hconst.2.1]
    exact he

private theorem realize_gate_rows (c : Circuit) (v : Nat → Nat) (V extra : NPolynomial)
    (w : Fin 7 → NPolynomial) (i : Fin c.gates.length)
    (hv : c.gates[i.val].ValidAt (c.inputCount+i.val))
    (he : v (c.inputCount+i.val)=gateValue v c.gates[i.val]) :
    RowsSolve (allocate (finalValues c v V extra w))
      (gateRows c.inputCount c.gates.length i.val c.gates[i.val]) := by
  let p := allocate (finalValues c v V extra w)
  have ho : p (c.inputCount+i.val)=C (v (c.inputCount+i.val)) :=
    final_wire c v V extra w _ (by omega)
  change RowsSolve p (gateRows c.inputCount c.gates.length i.val c.gates[i.val])
  cases htag : c.gates[i.val] with
  | constant k =>
      simp only [htag,gateValue] at he
      simp only [gateRows,rowsSolve_cons,rowsSolve_nil,and_true]
      norm_num [rowPolynomial,monomialPolynomial,wireMonomial,constant,ho,he,
        Narendran.Proof.signed_C,signed_natCast,Polynomial.C_eq_natCast,signed] <;> ring
  | add x y =>
      simp only [htag,Gate.ValidAt] at hv
      simp only [htag,gateValue] at he
      have hx : p x=C (v x) := final_wire c v V extra w x (by omega)
      have hy : p y=C (v y) := final_wire c v V extra w y (by omega)
      simp only [gateRows,rowsSolve_cons,rowsSolve_nil,and_true]
      norm_num [rowPolynomial,monomialPolynomial,wireMonomial,constant,ho,hx,hy,he,
        Narendran.Proof.signed_C,signed_natCast,Polynomial.C_eq_natCast] <;> ring
  | mul x y =>
      simp only [htag,Gate.ValidAt] at hv
      simp only [htag,gateValue] at he
      have hx : p x=C (v x) := final_wire c v V extra w x (by omega)
      have hy : p y=C (v y) := final_wire c v V extra w y (by omega)
      let s := (c.inputCount+c.gates.length)+c.inputCount+4*i.val
      let a := polynomialAux c.inputCount c.gates.length+12*i.val
      have hs0 : p s=C (v x+v y) := by
        simpa [htag,scalarValue,Nat.add_zero] using final_scalar c v V extra w i 0
      have hs1 : p (s+1)=C (triangularNat (v x)) := by
        simpa [htag,scalarValue] using final_scalar c v V extra w i 1
      have hs2 : p (s+2)=C (triangularNat (v y)) := by
        simpa [htag,scalarValue] using final_scalar c v V extra w i 2
      have hs3 : p (s+3)=C (triangularNat (v x+v y)) := by
        simpa [htag,scalarValue] using final_scalar c v V extra w i 3
      have hsq0 : (fun j : Fin 4 => p (a+j.val))=squareWitness (v x) := by
        funext j
        simpa [htag,squareInput,Nat.add_zero] using final_square c v V extra w i 0 j
      have hsq1 : (fun j : Fin 4 => p (a+4+j.val))=squareWitness (v y) := by
        funext j
        simpa [htag,squareInput] using final_square c v V extra w i 1 j
      have hsq2 : (fun j : Fin 4 => p (a+8+j.val))=squareWitness (v x+v y) := by
        funext j
        simpa [htag,squareInput] using final_square c v V extra w i 2 j
      change RowsSolve p
        ([[wireMonomial 1 0 s,wireMonomial (-1) 0 x,wireMonomial (-1) 0 y],
          [wireMonomial 1 0 (s+3),wireMonomial (-1) 0 (s+1),
           wireMonomial (-1) 0 (s+2),wireMonomial (-1) 0 (c.inputCount+i.val)]] ++
         squareRows x (s+1) a ++ squareRows y (s+2) (a+4) ++
         squareRows s (s+3) (a+8))
      simp only [List.append_assoc,rowsSolve_append,rowsSolve_cons,rowsSolve_nil,and_true]
      refine ⟨⟨?_,?_⟩,?_,?_,?_⟩
      · norm_num [rowPolynomial,monomialPolynomial,wireMonomial,constant,hs0,hx,hy,
          Narendran.Proof.signed_C,signed_natCast,Polynomial.C_eq_natCast] <;> ring
      · norm_num [rowPolynomial,monomialPolynomial,wireMonomial,constant,hs3,hs1,hs2,ho,
          CircuitLinear.Proof.triangular_addition,he,Narendran.Proof.signed_C,signed_natCast,Polynomial.C_eq_natCast] <;> ring
      · apply (CircuitLinear.Proof.square_rows_equations p x (s+1) a
          (v x) (triangularNat (v x)) hx hs1).mpr
        rw [hsq0]
        exact squareWitness_spec (v x)
      · apply (CircuitLinear.Proof.square_rows_equations p y (s+2) (a+4)
          (v y) (triangularNat (v y)) hy hs2).mpr
        rw [hsq1]
        exact squareWitness_spec (v y)
      · apply (CircuitLinear.Proof.square_rows_equations p s (s+3) (a+8)
          (v x+v y) (triangularNat (v x+v y)) hs0 hs3).mpr
        rw [hsq2]
        exact squareWitness_spec (v x+v y)

theorem literal_rows_forward : Targets.LiteralRowsForward := by
  intro c hc v hs
  obtain ⟨V,extra,w,hconstant⟩ := realize_constant_rows c v
  let p := allocate (finalValues c v V extra w)
  have hwire : ∀ j,j<c.inputCount+c.gates.length → p j=C (v j) :=
    final_wire c v V extra w
  refine ⟨p,hwire,?_⟩
  change RowsSolve p (inputRows c.inputCount c.gates.length ++
    (c.gates.zipIdx.flatMap fun gi => gateRows c.inputCount c.gates.length gi.2 gi.1) ++
    [[wireMonomial 1 0 c.leftOutput,wireMonomial (-1) 0 c.rightOutput]] ++
    constantRows (scalarCount c.inputCount c.gates.length) (constantAux c.inputCount c.gates.length))
  simp only [List.append_assoc,rowsSolve_append]
  refine ⟨?_,?_,?_,hconstant⟩
  · intro r hr
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
    have hin := List.mem_range.mp hi
    have hslack : p (c.inputCount+c.gates.length+i)=C (v i-1) :=
      final_slack c v V extra w ⟨i,hin⟩
    have hp : 0<v i := hs.1 i hin
    have hv : v i=(v i-1)+1 := by omega
    norm_num [rowPolynomial,monomialPolynomial,wireMonomial,constant,hwire i (by omega),
      hslack,Narendran.Proof.signed_C,signed_natCast,Polynomial.C_eq_natCast]
    rw [hv]
    push_cast
    ring
  · have hgate : ∀ gi∈c.gates.zipIdx,
        RowsSolve p (gateRows c.inputCount c.gates.length gi.2 gi.1) := by
      refine (List.forall_mem_zipIdx' (l := c.gates)
        (p := fun gi => RowsSolve p (gateRows c.inputCount c.gates.length gi.2 gi.1))).mpr ?_
      intro i hi
      exact realize_gate_rows c v V extra w ⟨i,hi⟩
        (valid_get c.inputCount c.gates hc.1 i hi)
        ((gatesHold_iff_get _ _ _).mp hs.2.1 i hi)
    intro r hr
    obtain ⟨gi,hgi,hr⟩ := List.mem_flatMap.mp hr
    exact hgate gi hgi r hr
  · simp only [rowsSolve_cons,rowsSolve_nil,and_true]
    norm_num [rowPolynomial,monomialPolynomial,wireMonomial,constant,
      hwire _ hc.2.1,hwire _ hc.2.2,hs.2.2]

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitFull.Proof
