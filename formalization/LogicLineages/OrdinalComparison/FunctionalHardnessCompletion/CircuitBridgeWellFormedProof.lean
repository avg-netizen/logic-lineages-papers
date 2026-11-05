module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitBridgeTargets
public import Mathlib.Data.List.Enum
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitLinear.Proof
open LogicLineages.ComputabilityKnowledge.CircuitReduction

private abbrev RowsBound (b : Nat) (rs : List Row) : Prop := WellFormedCode (b,rs)

private abbrev MonoBound (b : Nat) (m : MonomialCode) : Prop :=
  ∀ i,m.2.2=some i→i<b
private abbrev RowBound (b : Nat) (r : Row) : Prop := ∀m∈r,MonoBound b m
private theorem mono_wire (c : Int) (power index b : Nat) (hi : index<b) :
    MonoBound b (wireMonomial c power index) := by
  intro i he
  have h : index=i := Option.some.inj he
  omega
private theorem mono_constant (c : Int) (power b : Nat) : MonoBound b (constant c power) := by
  intro i he
  cases he
private theorem row_nil (b : Nat) : RowBound b [] := by intro m hm; cases hm
private theorem row_cons {b : Nat} {m : MonomialCode} {r : Row}
    (hm : MonoBound b m) (hr : RowBound b r) : RowBound b (m::r) := by
  intro x hx
  rcases List.mem_cons.mp hx with h | hx
  · subst x; exact hm
  · exact hr x hx
private theorem row_two {b : Nat} {a c : MonomialCode}
    (ha : MonoBound b a) (hc : MonoBound b c) : RowBound b [a,c] :=
  row_cons ha (row_cons hc (row_nil b))
private theorem row_three {b : Nat} {a c d : MonomialCode}
    (ha : MonoBound b a) (hc : MonoBound b c) (hd : MonoBound b d) : RowBound b [a,c,d] :=
  row_cons ha (row_cons hc (row_cons hd (row_nil b)))
private theorem row_four {b : Nat} {a c d e : MonomialCode}
    (ha : MonoBound b a) (hc : MonoBound b c) (hd : MonoBound b d) (he : MonoBound b e) :
    RowBound b [a,c,d,e] := row_cons ha (row_cons hc (row_cons hd (row_cons he (row_nil b))))
private theorem rows_nil (b : Nat) : RowsBound b [] := by intro r hr; cases hr
private theorem rows_cons {b : Nat} {r : Row} {rs : List Row}
    (hr : RowBound b r) (hrs : RowsBound b rs) : RowsBound b (r::rs) := by
  intro q hq
  rcases List.mem_cons.mp hq with h | hq
  · subst q; exact hr
  · exact hrs q hq
private theorem row_append {b : Nat} {r s : Row} (hr : RowBound b r) (hs : RowBound b s) :
    RowBound b (r++s) := by
  intro m hm
  rcases List.mem_append.mp hm with h | h
  · exact hr m h
  · exact hs m h
private theorem row_range (s b : Nat) (hs : s≤b) :
    RowBound b ((List.range s).map (wireMonomial 1 0)) := by
  intro m hm
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
  exact mono_wire _ _ _ _ (lt_of_lt_of_le (List.mem_range.mp hi) hs)

private theorem append_bound {b : Nat} {rs ss : List Row}
    (hr : RowsBound b rs) (hs : RowsBound b ss) : RowsBound b (rs++ss) := by
  intro row hrow
  rcases List.mem_append.mp hrow with h | h
  · exact hr row h
  · exact hs row h

private theorem valid_get (n : Nat) (gs : List Gate) (hv : ValidFrom n gs)
    (i : Nat) (hi : i<gs.length) : gs[i].ValidAt (n+i) := by
  induction gs generalizing n i with
  | nil => simp at hi
  | cons g gs ih =>
      obtain ⟨hg,hgs⟩ := hv
      cases i with
      | zero => simpa using hg
      | succ i =>
          have h := ih (n+1) hgs i (by simpa using hi)
          simpa only [List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm 1 i] using h

private theorem square_rows_bound (u v aux b : Nat)
    (hu : u<b) (hv : v<b) (ha : aux+4≤b) : RowsBound b (squareRows u v aux) := by
  unfold squareRows
  refine rows_cons (row_four ?_ ?_ ?_ ?_)
    (rows_cons (row_four ?_ ?_ ?_ ?_) (rows_cons (row_four ?_ ?_ ?_ ?_) (rows_nil _)))
  all_goals first | apply mono_wire <;> omega | exact mono_constant _ _ _

private theorem constant_rows_bound (s aux b : Nat)
    (hs : s≤b) (ha : aux+9≤b) : RowsBound b (constantRows s aux) := by
  have hlast : RowBound b ((List.range s).map (wireMonomial 1 0) ++
      [wireMonomial 1 0 (aux+1),wireMonomial (-1) 0 aux]) :=
    row_append (row_range s b hs)
      (row_two (mono_wire _ _ _ _ (by omega)) (mono_wire _ _ _ _ (by omega)))
  unfold constantRows
  refine rows_cons (row_four ?_ ?_ ?_ ?_) (rows_cons (row_four ?_ ?_ ?_ ?_)
    (rows_cons (row_four ?_ ?_ ?_ ?_) (rows_cons (row_four ?_ ?_ ?_ ?_)
      (rows_cons (row_four ?_ ?_ ?_ ?_) (rows_cons hlast (rows_nil _))))))
  all_goals first | apply mono_wire <;> omega | exact mono_constant _ _ _

private theorem input_rows_bound (n g b : Nat) (hb : n+g+n≤b) :
    RowsBound b (inputRows n g) := by
  intro r hr
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
  have hin := List.mem_range.mp hi
  refine row_three ?_ ?_ ?_
  all_goals first | apply mono_wire <;> omega | exact mono_constant _ _ _

private theorem gate_rows_bound (n g i : Nat) (gate : Gate) (hi : i<g)
    (hv : gate.ValidAt (n+i)) : RowsBound (unknownCount n g) (gateRows n g i gate) := by
  have hn : n+i<unknownCount n g := by
    simp only [unknownCount,constantAux,scalarCount]
    omega
  cases gate with
  | constant k =>
      unfold gateRows
      exact rows_cons (row_two (mono_wire _ _ _ _ hn) (mono_constant _ _ _)) (rows_nil _)
  | add x y =>
      obtain ⟨hx,hy⟩ := hv
      unfold gateRows
      refine rows_cons (row_three ?_ ?_ ?_) (rows_nil _)
      all_goals apply mono_wire <;> omega
  | mul x y =>
      obtain ⟨hx,hy⟩ := hv
      have hxb : x<unknownCount n g := by omega
      have hyb : y<unknownCount n g := by omega
      have hsb : (n+g)+n+4*i+3<unknownCount n g := by
        simp only [unknownCount,constantAux,scalarCount]
        omega
      have hab : polynomialAux n g+12*i+12≤unknownCount n g := by
        simp only [unknownCount,constantAux,polynomialAux,scalarCount]
        omega
      change RowsBound (unknownCount n g)
        ([[wireMonomial 1 0 ((n+g)+n+4*i),wireMonomial (-1) 0 x,wireMonomial (-1) 0 y],
          [wireMonomial 1 0 ((n+g)+n+4*i+3),wireMonomial (-1) 0 ((n+g)+n+4*i+1),
           wireMonomial (-1) 0 ((n+g)+n+4*i+2),wireMonomial (-1) 0 (n+i)]] ++
         squareRows x ((n+g)+n+4*i+1) (polynomialAux n g+12*i) ++
         squareRows y ((n+g)+n+4*i+2) (polynomialAux n g+12*i+4) ++
         squareRows ((n+g)+n+4*i) ((n+g)+n+4*i+3) (polynomialAux n g+12*i+8))
      simp only [List.append_assoc]
      apply append_bound
      · refine rows_cons (row_three ?_ ?_ ?_) (rows_cons (row_four ?_ ?_ ?_ ?_) (rows_nil _))
        all_goals apply mono_wire <;> omega
      · exact append_bound (square_rows_bound _ _ _ _ hxb (by omega) (by omega))
          (append_bound (square_rows_bound _ _ _ _ hyb (by omega) (by omega))
            (square_rows_bound _ _ _ _ (by omega) hsb (by omega)))

/-- Every reference in the literal system refers to the one declared shared
unknown block, including all otherwise-unused reserve slots and all outputs. -/
theorem circuit_system_wellFormed (c : Circuit) (hc : c.WellFormed) :
    WellFormedCode (encodeCircuitSystem c) := by
  obtain ⟨hvalid,hleft,hright⟩ := hc
  have hgates : RowsBound (unknownCount c.inputCount c.gates.length)
      (c.gates.zipIdx.flatMap fun gi => gateRows c.inputCount c.gates.length gi.2 gi.1) := by
    have hv : ∀ gi ∈ c.gates.zipIdx, gi.1.ValidAt (c.inputCount+gi.2) :=
      List.forall_mem_zipIdx'.mpr (fun i hi => valid_get c.inputCount c.gates hvalid i hi)
    intro row hrow
    obtain ⟨gi,hgi,hrow⟩ := List.mem_flatMap.mp hrow
    exact gate_rows_bound _ _ _ _ (List.snd_lt_of_mem_zipIdx hgi) (hv gi hgi) row hrow
  have hsize : c.inputCount+c.gates.length+c.inputCount ≤
      unknownCount c.inputCount c.gates.length := by
    simp only [unknownCount,constantAux,scalarCount]
    omega
  unfold encodeCircuitSystem
  change RowsBound _ _
  simp only [List.append_assoc]
  change RowsBound _ (inputRows _ _ ++ (_ ++ (_ ++ _)))
  apply append_bound (input_rows_bound _ _ _ hsize)
  apply append_bound hgates
  apply append_bound
  · refine rows_cons (row_two ?_ ?_) (rows_nil _)
    all_goals apply mono_wire <;> omega
  · exact constant_rows_bound _ _ _ (by
        simp only [unknownCount,constantAux,scalarCount]; omega) (by simp [unknownCount])

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitLinear.Proof
