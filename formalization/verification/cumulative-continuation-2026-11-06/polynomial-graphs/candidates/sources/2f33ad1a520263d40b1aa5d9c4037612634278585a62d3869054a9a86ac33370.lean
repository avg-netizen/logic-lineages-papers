module
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.Targets
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionTargets
import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionSupportProof

public section
namespace LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionNodeProof
open ExpressionSupportProof

theorem valid_add {a b : Expr} (h : ValidExpr (.add a b)) : ValidExpr a ∧ ValidExpr b :=
  ⟨fun code hc => h code (List.mem_append_left _ hc),
    fun code hc => h code (List.mem_append_right _ hc)⟩

theorem valid_scale {k : Nat} {a : Expr} (h : ValidExpr (.scale k a)) : ValidExpr a := h

theorem valid_collapse {code : Nat} {a : Expr} (h : ValidExpr (.collapse code a)) :
    ValidExpr a ∧ ValidHead code :=
  ⟨fun q hq => h q (List.mem_append_left _ hq),
    h code (List.mem_append_right _ (List.mem_singleton_self _))⟩

theorem numeral_domain (z n : Nat) (ν : Nat → Nat) : RowDomain (numeralRow z n) ν := by
  simp [RowDomain,numeralRow,WordDomain]

theorem variable_domain (z i : Nat) (ν : Nat → Nat) : RowDomain (variableRow z i) ν := by
  simp [RowDomain,variableRow,WordDomain]

theorem addition_domain (z x y : Nat) (ν : Nat → Nat) : RowDomain (additionRow z x y) ν := by
  simp [RowDomain,additionRow,WordDomain]

theorem scale_domain (z k x : Nat) (ν : Nat → Nat) : RowDomain (scaleRow z k x) ν := by
  simp [RowDomain,scaleRow,WordDomain]

theorem numeral_allowed (D z n : Nat) : RowAllowed D (numeralRow z n) := by
  simp [RowAllowed,numeralRow,WordAllowed]

theorem variable_allowed (D z i : Nat) : RowAllowed D (variableRow z i) := by
  simp [RowAllowed,variableRow,WordAllowed]

theorem addition_allowed (D z x y : Nat) : RowAllowed D (additionRow z x y) := by
  simp [RowAllowed,additionRow,WordAllowed]

theorem scale_allowed (D z k x : Nat) : RowAllowed D (scaleRow z k x) := by
  simp [RowAllowed,scaleRow,WordAllowed]

theorem numeral_equation (z n : Nat) (ν : Nat → Nat) :
    RowValue (numeralRow z n) ν = 0 ↔ ν z = n := by
  simp only [numeralRow,RowValue,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,wordValue,one_mul,add_zero]
  omega

theorem variable_equation (z i : Nat) (ν : Nat → Nat) :
    RowValue (variableRow z i) ν = 0 ↔ ν z = ν i := by
  simp only [variableRow,RowValue,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,wordValue,one_mul,neg_one_mul,add_zero,zero_add]
  omega

theorem addition_equation (z x y : Nat) (ν : Nat → Nat) :
    RowValue (additionRow z x y) ν = 0 ↔ ν z = ν x + ν y := by
  simp only [additionRow,RowValue,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,wordValue,one_mul,neg_one_mul,add_zero,zero_add]
  omega

theorem scale_equation (z k x : Nat) (ν : Nat → Nat) :
    RowValue (scaleRow z k x) ν = 0 ↔ ν z = k * ν x := by
  simp only [scaleRow,RowValue,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,wordValue,one_mul,neg_mul,add_zero,zero_add,← Nat.cast_mul]
  omega

theorem rows_hold_append (rs ss : List Row) (ν : Nat → Nat) :
    RowsHold (rs++ss) ν ↔ RowsHold rs ν ∧ RowsHold ss ν := by
  constructor
  · intro h
    exact ⟨fun row hr => h row (List.mem_append_left _ hr),
      fun row hr => h row (List.mem_append_right _ hr)⟩
  · rintro ⟨hrs,hss⟩ row hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hrs row hr
    · exact hss row hr

theorem rows_hold_singleton (row : Row) (ν : Nat → Nat) :
    RowsHold [row] ν ↔ RowDomain row ν ∧ RowValue row ν = 0 := by
  simp only [RowsHold,List.mem_singleton,forall_eq]

theorem graph_numeral (start n : Nat) (ν : Nat → Nat) :
    GraphHolds start (.numeral n) ν ↔ ν start = n := by
  simp only [GraphHolds,rows,rows_hold_singleton,numeral_domain,true_and,numeral_equation]

theorem graph_variable (start i : Nat) (ν : Nat → Nat) :
    GraphHolds start (.variable i) ν ↔ ν start = ν i := by
  simp only [GraphHolds,rows,rows_hold_singleton,variable_domain,true_and,variable_equation]

theorem graph_add (start : Nat) (a b : Expr) (ν : Nat → Nat) :
    GraphHolds start (.add a b) ν ↔
      GraphHolds start a ν ∧ GraphHolds (start+nodeCount a) b ν ∧
      ν (output start (.add a b)) = ν (output start a) + ν (output (start+nodeCount a) b) := by
  simp only [GraphHolds,rows,rows_hold_append,rows_hold_singleton,
    addition_domain,true_and,addition_equation,and_assoc]

theorem graph_scale (start k : Nat) (a : Expr) (ν : Nat → Nat) :
    GraphHolds start (.scale k a) ν ↔ GraphHolds start a ν ∧
      ν (output start (.scale k a)) = k * ν (output start a) := by
  simp only [GraphHolds,rows,rows_hold_append,rows_hold_singleton,
    scale_domain,true_and,scale_equation]

theorem graph_collapse (hHead : Targets.HeadEquationExact) (start code : Nat)
    (a : Expr) (hc : ValidHead code) (ν : Nat → Nat) :
    GraphHolds start (.collapse code a) ν ↔ GraphHolds start a ν ∧
      ν (output start (.collapse code a)) = headValue code (ν (output start a)) := by
  have hh := (hHead code hc (output start a) (output start (.collapse code a))).2 ν
  simp only [GraphHolds,rows,rows_hold_append,rows_hold_singleton]
  constructor
  · rintro ⟨ha,_,hout⟩
    exact ⟨ha,hh.2.mp hout⟩
  · rintro ⟨ha,hout⟩
    exact ⟨ha,hh.1,hh.2.mpr hout⟩

theorem graphSoundness (hHead : Targets.HeadEquationExact) :
    ExpressionTargets.GraphSoundness := by
  intro start t
  induction t generalizing start with
  | numeral n =>
      intro ht ν h
      simpa only [output,nodeCount,Nat.add_sub_cancel,Expr.value] using
        (graph_numeral start n ν).mp h
  | «variable» i =>
      intro ht ν h
      simpa only [output,nodeCount,Nat.add_sub_cancel,Expr.value] using
        (graph_variable start i ν).mp h
  | add a b iha ihb =>
      intro ht ν h
      obtain ⟨ha,hb,hout⟩ := (graph_add start a b ν).mp h
      have hvalid := valid_add ht
      rw [iha start hvalid.1 ν ha,ihb (start+nodeCount a) hvalid.2 ν hb] at hout
      exact hout
  | scale k a ih =>
      intro ht ν h
      obtain ⟨ha,hout⟩ := (graph_scale start k a ν).mp h
      rw [ih start (valid_scale ht) ν ha] at hout
      exact hout
  | collapse code a ih =>
      intro ht ν h
      have hvalid := valid_collapse ht
      obtain ⟨ha,hout⟩ := (graph_collapse hHead start code a hvalid.2 ν).mp h
      rw [ih start hvalid.1 ν ha] at hout
      exact hout

end LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionNodeProof
