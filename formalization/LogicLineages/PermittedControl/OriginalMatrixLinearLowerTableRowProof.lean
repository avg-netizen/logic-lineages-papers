module
public import LogicLineages.PermittedControl.OriginalMatrixLinearLowerTableTargets
import LogicLineages.PermittedControl.OriginalMatrixLinearLowerTableProof
import LogicLineages.PermittedControl.PreparedParameterActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMatrixLinearLowerTable
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open HeterogeneousSignedMatrixSlice (Row)
open PreparedProjection (LowerOperand LowerOperandActual lowerOperandRead PreparedTableTied preparedTiedProjection)
open MixedSameRankResidue (WeightedOperand orderedReads actualSum)
open ActualMixedRowLeadingAnnotations (LinearOperand)

private theorem slotSpec (ops : List LowerOperand) (op : LowerOperand) (used : op ∈ ops) :
    ∃ j : Nat, ∃ hj : j < ops.length, slot ops op = j+1 ∧ ops[j] = op := by
  let has : ∃ i : Nat, ∃ hi : i < ops.length, ops[i] = op := List.mem_iff_getElem.mp used
  let j := Classical.choose has
  obtain ⟨hj,eq⟩ := Classical.choose_spec has
  exact ⟨j,hj,by rw [slot,dif_pos used] <;> rfl,eq⟩

private theorem identityRead (f ρ : Nat → Nat) (op : LowerOperand) (linear : LinearOperand op) :
    LowerOperandActual f ρ op (ρ op.rank) := by
  cases op with
  | coordinate rank => rfl
  | count rank lam mu => exact False.elim linear
  | ordinary rank F =>
      cases F with
      | entry k lam mu => exact False.elim linear
      | iterate k =>
          cases k with
          | succ k => exact False.elim linear
          | zero => exact ⟨True.intro,rfl⟩

private theorem evaluateTerm (f ρ : Nat → Nat) (top : Nat) (rs : List Row) (row : Row) (hr : row ∈ rs)
    (shape : TopLinear top rs) (ν : Nat → Nat) (fit : PreparedTableTied f top ρ (lowerTable top rs) ν)
    (t : WeightedOperand) (ht : t ∈ row.2.2) (z : Nat) :
    let name := nameAt top (lowerTable top rs) t.2
    let v := Function.update ν 0 z name
    name ≤ (lowerTable top rs).length ∧
    LowerOperandActual f (Function.update ρ top z) t.2 v ∧
    lowerOperandRead f (Function.update ρ top z) t.2 = some (some v) := by
  obtain ⟨le,bare⟩ := shape row hr t ht
  by_cases htop : t.2.rank = top
  · have actual : LowerOperandActual f (Function.update ρ top z) t.2
        (Function.update ν 0 z 0) := by
      simpa only [htop,Function.update_self] using
        identityRead f (Function.update ρ top z) t.2 (bare htop)
    simp only [nameAt,if_pos htop]
    exact ⟨Nat.zero_le _,actual,(preparedTiedProjection.1 f _ _ _).mpr actual⟩
  · have lower : t.2.rank < top := lt_of_le_of_ne le htop
    obtain ⟨j,hj,slotEq,opEq⟩ := slotSpec _ t.2 (lowerMember top rs row hr t ht lower)
    have h0 : LowerOperandActual f ρ t.2 (ν (j+1)) := by
      have real := (fit j hj).2
      change LowerOperandActual f ρ (lowerTable top rs)[j] (ν (j+1)) at real
      rwa [opEq] at real
    have h := (preparedTiedProjection.1 f ρ t.2 _).mpr h0
    have hit : lowerOperandRead f (Function.update ρ top z) t.2 = some (some (ν (j+1))) :=
      (lowerReadStable f ρ top z t.2 lower).trans h
    simp only [nameAt,if_neg htop,slotEq,Function.update_of_ne (Nat.succ_ne_zero j)]
    exact ⟨Nat.succ_le_of_lt hj,(preparedTiedProjection.1 f _ _ _).mp hit,hit⟩

private theorem aligned (f θ : Nat → Nat) (read : WeightedOperand → Nat) (ts : List WeightedOperand)
    (facts : ∀ t ∈ ts, LowerOperandActual f θ t.2 (read t) ∧
      lowerOperandRead f θ t.2 = some (some (read t))) (vs : List Nat) :
    orderedReads f θ ts vs ↔ vs = ts.map read := by
  induction ts generalizing vs with
  | nil => cases vs <;> simp [orderedReads]
  | cons t ts ih =>
      cases vs with
      | nil => simp [orderedReads]
      | cons v vs =>
          obtain ⟨real,hit⟩ := facts t List.mem_cons_self
          have rest := ih (fun u hu => facts u (List.mem_cons_of_mem _ hu)) vs
          constructor
          · intro h
            have eq : read t = v := Option.some.inj (Option.some.inj (hit.symm.trans h.2.1))
            exact congrArg₂ List.cons eq.symm (rest.mp h.2.2)
          · intro h
            have tail := List.cons.inj h
            rw [tail.1]
            exact ⟨real,hit,rest.mpr tail.2⟩

private theorem sumEval (name : LowerOperand → Nat) (ν : Nat → Nat) (ts : List WeightedOperand) :
    actualSum ts (ts.map (fun t => ν (name t.2))) =
      (ts.map (fun t => t.1 * (ν (name t.2) : Int))).sum := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      change t.1 * (ν (name t.2) : Int) + actualSum ts _ =
        t.1 * (ν (name t.2) : Int) + (ts.map (fun t => t.1 * (ν (name t.2) : Int))).sum
      rw [ih]

theorem exactLinearPreparedRow : ExactLinearPreparedRow := by
  intro f ρ top rows shape row hr
  let ops := lowerTable top rows
  let name := nameAt top ops
  have hname (t : WeightedOperand) (ht : t ∈ row.2.2) : name t.2 ≤ ops.length := by
    obtain ⟨le,bare⟩ := shape row hr t ht
    by_cases eq : t.2.rank = top
    · simp [name,nameAt,eq]
    · obtain ⟨j,hj,slotEq,_⟩ := slotSpec ops t.2 (lowerMember top rows row hr t ht (lt_of_le_of_ne le eq))
      simp only [name,nameAt,if_neg eq,slotEq]
      exact Nat.succ_le_of_lt hj
  refine ⟨?_,?_⟩
  · intro n hn
    change n ∈ (row.2.2.map (fun t => (t.1,NormalForm.Summand.variable (name t.2)))).map
      (fun a => a.2.name) at hn
    obtain ⟨term,whereTerm,eq⟩ := List.mem_map.mp hn
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp whereTerm
    rw [← eq]
    exact hname t ht
  · intro ν fit z v
    let updated := Function.update ν 0 z
    let read : WeightedOperand → Nat := fun t => updated (name t.2)
    have all (t : WeightedOperand) (ht : t ∈ row.2.2) :
        LowerOperandActual f (Function.update ρ top z) t.2 (read t) ∧
          lowerOperandRead f (Function.update ρ top z) t.2 = some (some (read t)) :=
      (evaluateTerm f ρ top rows row hr shape ν fit t ht z).2
    have sum : NormalForm.rowValue (preparedRow top ops row) updated =
        row.2.1 + actualSum row.2.2 (row.2.2.map read) := by
      unfold preparedRow NormalForm.rowValue
      simp only [List.map_map,Function.comp_def,NormalForm.Summand.term,Term.value]
      rw [sumEval name updated row.2.2] <;> rfl
    change (∃ vs, orderedReads f (Function.update ρ top z) row.2.2 vs ∧
      row.2.1 + actualSum row.2.2 vs = v) ↔ _
    rw [sum]
    constructor
    · rintro ⟨vs,live,value⟩
      have eq := (aligned f (Function.update ρ top z) read row.2.2 all vs).mp live
      rwa [eq] at value
    · intro value
      exact ⟨row.2.2.map read,
        (aligned f (Function.update ρ top z) read row.2.2 all _).mpr rfl,value⟩

end LogicLineages.PermittedControl.OriginalMatrixLinearLowerTable
