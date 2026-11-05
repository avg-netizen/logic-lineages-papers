module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitFullRunProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitGadgetConstantProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitFull.Proof
open Polynomial CircuitLinear Narendran
open LogicLineages.ComputabilityKnowledge.CircuitReduction

private theorem signed_natCast (n : Nat) : signed (n : NPolynomial)=C (n : Int) := by
  simp [signed]

@[simp] theorem rowsSolve_append (p : Nat → NPolynomial) (a b : List Row) :
    RowsSolve p (a++b) ↔ RowsSolve p a ∧ RowsSolve p b := by
  constructor
  · intro h
    exact ⟨fun r hr => h r (List.mem_append_left _ hr),
      fun r hr => h r (List.mem_append_right _ hr)⟩
  · rintro ⟨ha,hb⟩ r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact ha r hr
    · exact hb r hr

@[simp] theorem rowsSolve_cons (p : Nat → NPolynomial) (a : Row) (b : List Row) :
    RowsSolve p (a::b) ↔ rowPolynomial p a=0 ∧ RowsSolve p b := by
  simp [RowsSolve]

@[simp] theorem rowsSolve_nil (p : Nat → NPolynomial) : RowsSolve p [] := by
  intro r hr
  cases hr

private theorem scalar_index (n g i j : Nat) (hi : i<g) (hj : j<4) :
    (n+g)+n+4*i+j<scalarCount n g := by unfold scalarCount; omega

/-- Decoding a multiplication row uses the same constants in all three square
instances, including repeated inputs. It does not require positive slack slots. -/
theorem gate_rows_sound (p : Nat → NPolynomial) (n g i : Nat) (gate : Gate)
    (v : Nat → Nat) (hc : ∀ j,j<scalarCount n g → p j=C (v j))
    (hi : i<g) (hv : gate.ValidAt (n+i)) (hr : RowsSolve p (gateRows n g i gate)) :
    v (n+i)=gateValue v gate := by
  have ho : p (n+i)=C (v (n+i)) := hc _ (by unfold scalarCount;omega)
  cases gate with
  | constant k =>
      have h := hr _ (List.mem_singleton_self _)
      have hh := congrArg (fun q : ZPolynomial => q.coeff 0) h
      norm_num [rowPolynomial,monomialPolynomial,wireMonomial,constant,ho,
        Narendran.Proof.signed_C,signed_natCast] at hh
      change v (n+i)=k+1
      omega
  | add x y =>
      obtain ⟨hx,hy⟩ := hv
      have hxc := hc x (by unfold scalarCount;omega)
      have hyc := hc y (by unfold scalarCount;omega)
      have h := hr _ (List.mem_singleton_self _)
      have hh := congrArg (fun q : ZPolynomial => q.coeff 0) h
      norm_num [rowPolynomial,monomialPolynomial,wireMonomial,constant,ho,hxc,hyc,
        Narendran.Proof.signed_C,signed_natCast] at hh
      change v (n+i)=v x+v y
      omega
  | mul x y =>
      obtain ⟨hx,hy⟩ := hv
      let s := (n+g)+n+4*i
      let a := polynomialAux n g+12*i
      have hxc := hc x (by unfold scalarCount;omega)
      have hyc := hc y (by unfold scalarCount;omega)
      have hs : ∀ j,j<4 → p (s+j)=C (v (s+j)) := by
        intro j hj
        exact hc _ (scalar_index n g i j hi hj)
      change RowsSolve p
        ([[wireMonomial 1 0 s,wireMonomial (-1) 0 x,wireMonomial (-1) 0 y],
          [wireMonomial 1 0 (s+3),wireMonomial (-1) 0 (s+1),
           wireMonomial (-1) 0 (s+2),wireMonomial (-1) 0 (n+i)]] ++
         squareRows x (s+1) a ++ squareRows y (s+2) (a+4) ++
         squareRows s (s+3) (a+8)) at hr
      simp only [List.append_assoc,rowsSolve_append,rowsSolve_cons,rowsSolve_nil,and_true] at hr
      obtain ⟨⟨hadd,hout⟩,h1,h2,h3⟩ := hr
      have ha := congrArg (fun q : ZPolynomial => q.coeff 0) hadd
      have hb := congrArg (fun q : ZPolynomial => q.coeff 0) hout
      have hs0 := hs 0 (by decide)
      simp only [Nat.add_zero] at hs0
      have hs1 := hs 1 (by decide)
      have hs2 := hs 2 (by decide)
      have hs3 := hs 3 (by decide)
      norm_num [rowPolynomial,monomialPolynomial,wireMonomial,constant,ho,hxc,hyc,
        hs0,hs1,hs2,hs3,Narendran.Proof.signed_C,signed_natCast] at ha hb
      have hsum : v s=v x+v y := by omega
      have hout' : v (s+3)=v (s+1)+v (s+2)+v (n+i) := by omega
      have hsq1 := (Narendran.Proof.exactSquareGadget (v x) (v (s+1))).mp
        ⟨_,(CircuitLinear.Proof.square_rows_equations p x (s+1) a (v x) (v (s+1)) hxc hs1).mp h1⟩
      have hsq2 := (Narendran.Proof.exactSquareGadget (v y) (v (s+2))).mp
        ⟨_,(CircuitLinear.Proof.square_rows_equations p y (s+2) (a+4) (v y) (v (s+2)) hyc hs2).mp h2⟩
      have hsq3 := (Narendran.Proof.exactSquareGadget (v s) (v (s+3))).mp
        ⟨_,(CircuitLinear.Proof.square_rows_equations p s (s+3) (a+8) (v s) (v (s+3)) hs0 hs3).mp h3⟩
      rw [hsum] at hsq3
      exact CircuitLinear.Proof.triangular_multiplication (v x) (v y) (v (n+i))
        (v (s+1)) (v (s+2)) (v (s+3)) hsq1 hsq2 hsq3 hout'

theorem literal_rows_backward : Targets.LiteralRowsBackward := by
  intro c hc p hp
  have hparts : RowsSolve p (inputRows c.inputCount c.gates.length) ∧
      RowsSolve p (c.gates.zipIdx.flatMap fun gi => gateRows c.inputCount c.gates.length gi.2 gi.1) ∧
      RowsSolve p [[wireMonomial 1 0 c.leftOutput,wireMonomial (-1) 0 c.rightOutput]] ∧
      RowsSolve p (constantRows (scalarCount c.inputCount c.gates.length)
        (constantAux c.inputCount c.gates.length)) := by
    simpa only [encodeCircuitSystem,List.append_assoc,rowsSolve_append] using hp
  obtain ⟨hin,hg,hout,hconst⟩ := hparts
  let v : Nat → Nat := fun i => (p i).coeff 0
  have hconstants : ∀ j,j<scalarCount c.inputCount c.gates.length → p j=C (v j) := by
    intro j hj
    obtain ⟨k,hk⟩ := CircuitLinear.Proof.constant_rows_force_scalars p
      (scalarCount c.inputCount c.gates.length) (constantAux c.inputCount c.gates.length) hconst j hj
    simp [v,hk]
  have hwire : ∀ j,j<c.inputCount+c.gates.length → p j=C (v j) := by
    intro j hj
    exact hconstants j (by unfold scalarCount;omega)
  refine ⟨v,⟨?_,?_,?_⟩,hwire⟩
  · intro i hi
    have h := hin _ (List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩)
    have hslack := hconstants (c.inputCount+c.gates.length+i) (by unfold scalarCount;omega)
    have hh := congrArg (fun q : ZPolynomial => q.coeff 0) h
    norm_num [rowPolynomial,monomialPolynomial,wireMonomial,constant,hwire i (by omega),
      hslack,Narendran.Proof.signed_C,signed_natCast] at hh
    omega
  · apply (gatesHold_iff_zipIdx _ _ _).mpr
    intro gi hgi
    have hall : ∀ gj∈c.gates.zipIdx,gj.1.ValidAt (c.inputCount+gj.2) :=
      List.forall_mem_zipIdx'.mpr (fun i hi => valid_get c.inputCount c.gates hc.1 i hi)
    have hvalid := hall gi hgi
    apply gate_rows_sound p c.inputCount c.gates.length gi.2 gi.1 v hconstants
      (List.snd_lt_of_mem_zipIdx hgi) hvalid
    intro r hr
    exact hg r (List.mem_flatMap.mpr ⟨gi,hgi,hr⟩)
  · have h := hout _ (List.mem_singleton_self _)
    have hh := congrArg (fun q : ZPolynomial => q.coeff 0) h
    norm_num [rowPolynomial,monomialPolynomial,wireMonomial,constant,hwire _ hc.2.1,
      hwire _ hc.2.2,Narendran.Proof.signed_C,signed_natCast] at hh
    omega

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitFull.Proof
