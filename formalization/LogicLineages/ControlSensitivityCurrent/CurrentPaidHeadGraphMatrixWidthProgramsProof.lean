module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphMatrixCodeDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.FiniteGraphProof
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundAnnotationMarkerProgramsProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.MatrixCode

open LogicLineages.OrdinalComparison.LayeredComparison.FiniteGraph.Proof (exactDecreasingGraph)
open CurrentGroundAnnotationPrograms (chooseProgram)

theorem tagProgram : Primrec (fun n : Nat => n%8) := Primrec.nat_mod.comp Primrec.id (Primrec.const 8)
theorem digitProgram : Primrec (fun n : Nat => n/8) := Primrec.nat_div.comp Primrec.id (Primrec.const 8)
theorem leftProgram : Primrec (fun n : Nat => (n/8).unpair.1) := Primrec.fst.comp (Primrec.unpair.comp digitProgram)
theorem rightProgram : Primrec (fun n : Nat => (n/8).unpair.2) := Primrec.snd.comp (Primrec.unpair.comp digitProgram)
theorem isTag (t : Nat) : PrimrecPred (fun n : Nat => n%8=t) := Primrec.eq.comp tagProgram (Primrec.const t)
theorem clusteredTag : PrimrecPred (fun n : Nat => 5 ≤ n%8) := Primrec.nat_le.comp (Primrec.const 5) tagProgram

theorem singleProgram {A B} [Primcodable A] [Primcodable B] {a : A → B} (ha : Primrec a) :
    Primrec (fun x => [a x]) := Primrec.list_cons.comp ha (Primrec.const [])
theorem pairListProgram {A B} [Primcodable A] [Primcodable B] {a b : A → B}
    (ha : Primrec a) (hb : Primrec b) : Primrec (fun x => [a x,b x]) :=
  Primrec.list_cons.comp ha (singleProgram hb)

def childTerm (n : Nat) : List Nat :=
  if n%8=2 then [(n/8).unpair.1,(n/8).unpair.2]
  else if n%8=4 then [(n/8).unpair.2] else []

def childFormula (n : Nat) : List Nat :=
  if 5 ≤ n%8 then
    if n%8=5 then [n/8] else [(n/8).unpair.1,(n/8).unpair.2]
  else []

theorem termChildProgram : Primrec childTerm :=
  Primrec.ite (isTag 2) (pairListProgram leftProgram rightProgram)
    (Primrec.ite (isTag 4) (singleProgram rightProgram) (Primrec.const []))
theorem formulaChildProgram : Primrec childFormula :=
  Primrec.ite clusteredTag (Primrec.ite (isTag 5) (singleProgram digitProgram)
    (pairListProgram leftProgram rightProgram)) (Primrec.const [])

theorem termChildDecrease (n k : Nat) (hk : k∈childTerm n) : k<n := by
  unfold childTerm at hk
  split at hk
  · rename_i hd
    have hn : n/8<n := Nat.div_lt_self (by omega) (by decide)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl
    · exact (Nat.unpair_left_le _).trans_lt hn
    · exact (Nat.unpair_right_le _).trans_lt hn
  · split at hk
    · rename_i hd
      have hn : n/8<n := Nat.div_lt_self (by omega) (by decide)
      simp only [List.mem_singleton] at hk
      subst k
      exact (Nat.unpair_right_le _).trans_lt hn
    · simp at hk

theorem formulaChildDecrease (n k : Nat) (hk : k∈childFormula n) : k<n := by
  unfold childFormula at hk
  split at hk
  · rename_i ht
    have hn : n/8<n := Nat.div_lt_self (by omega) (by decide)
    split at hk
    · simpa only [List.mem_singleton.mp hk] using hn
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl|rfl
      · exact (Nat.unpair_left_le _).trans_lt hn
      · exact (Nat.unpair_right_le _).trans_lt hn
  · simp at hk

/-- A separate finite rank pass computes only how many arithmetic witnesses
are inserted, independently of an initial offset. Used to index the actual
raw emitter's second child without presuming a higher-order runner. -/
def termWidth (n : Nat) : Nat :=
  if h : n%8=2 ∨ n%8=4 then
    have hn : n/8<n := Nat.div_lt_self (by omega) (by decide)
    have hl : (n/8).unpair.1<n := (Nat.unpair_left_le _).trans_lt hn
    have hr : (n/8).unpair.2<n := (Nat.unpair_right_le _).trans_lt hn
    if n%8=2 then termWidth (n/8).unpair.1+termWidth (n/8).unpair.2+1
    else termWidth (n/8).unpair.2+2
  else if n%8=0 then 0 else 1
termination_by n
decreasing_by all_goals assumption

def formulaWidth (n : Nat) : Nat :=
  if h : 5 ≤ n%8 then
    have hn : n/8<n := Nat.div_lt_self (by omega) (by decide)
    have hl : (n/8).unpair.1<n := (Nat.unpair_left_le _).trans_lt hn
    have hr : (n/8).unpair.2<n := (Nat.unpair_right_le _).trans_lt hn
    if n%8=5 then formulaWidth (n/8) else formulaWidth (n/8).unpair.1+formulaWidth (n/8).unpair.2
  else if 2 ≤ n%8 then termWidth (n/8).unpair.1+termWidth (n/8).unpair.2 else 0
termination_by n
decreasing_by all_goals assumption

private def assembleWidth (n : Nat) (ls : List Nat) : Nat :=
  if n%8=2 then ls.getD 0 0+ls.getD 1 0+1 else if n%8=4 then ls.getD 0 0+2
  else if n%8=0 then 0 else 1

private theorem widthParts : Primrec₂ assembleWidth := by
  let X := Nat×List Nat
  have p (i : Nat) : Primrec (fun q : X => q.2.getD i 0) := (Primrec.list_getD 0).comp Primrec.snd (Primrec.const i)
  have l := Primrec.nat_add.comp (Primrec.nat_add.comp (p 0) (p 1)) (Primrec.const 1)
  have r := Primrec.nat_add.comp (p 0) (Primrec.const 2)
  exact Primrec.ite ((isTag 2).comp Primrec.fst) l
    (Primrec.ite ((isTag 4).comp Primrec.fst) r
      (Primrec.ite ((isTag 0).comp Primrec.fst) (Primrec.const 0) (Primrec.const 1)))

private theorem widthEq (n : Nat) : termWidth n=assembleWidth n ((childTerm n).map termWidth) := by
  rw [termWidth]
  by_cases h2 : n%8=2 <;> by_cases h4 : n%8=4 <;>
    simp [childTerm,assembleWidth,h2,h4]

theorem termWidthProgram : Computable termWidth :=
  (exactDecreasingGraph Nat Nat childTerm assembleWidth id termChildProgram.to_comp widthParts.to_comp
    Computable.id termWidth termChildDecrease widthEq).2

private def assembleForm (n : Nat) (ls : List Nat) : Nat :=
  if 5≤n%8 then if n%8=5 then ls.getD 0 0 else ls.getD 0 0+ls.getD 1 0
  else if 2≤n%8 then termWidth (n/8).unpair.1+termWidth (n/8).unpair.2 else 0

private theorem formWidthParts : Computable₂ assembleForm := by
  let X := Nat×List Nat
  have p (i : Nat) : Primrec (fun q : X => q.2.getD i 0) := (Primrec.list_getD 0).comp Primrec.snd (Primrec.const i)
  have h := Primrec.nat_add.to_comp.comp
    (termWidthProgram.comp (leftProgram.comp (Primrec.fst : Primrec (fun q : X => q.1))).to_comp)
    (termWidthProgram.comp (rightProgram.comp (Primrec.fst : Primrec (fun q : X => q.1))).to_comp)
  exact chooseProgram (clusteredTag.comp Primrec.fst)
    (chooseProgram ((isTag 5).comp Primrec.fst) (p 0).to_comp (Primrec.nat_add.comp (p 0) (p 1)).to_comp)
    (chooseProgram (Primrec.nat_le.comp (Primrec.const 2) (tagProgram.comp Primrec.fst)) h (Computable.const 0))

private theorem formWidthEq (n : Nat) : formulaWidth n=assembleForm n ((childFormula n).map formulaWidth) := by
  rw [formulaWidth]
  by_cases h : 5≤n%8 <;> by_cases h5 : n%8=5 <;> simp [h,h5,childFormula,assembleForm]

theorem formulaWidthProgram : Computable formulaWidth :=
  (exactDecreasingGraph Nat Nat childFormula assembleForm id formulaChildProgram.to_comp formWidthParts
    Computable.id formulaWidth formulaChildDecrease formWidthEq).2

theorem exactTermWidth (off n : Nat) : (emitTerm off n).2.1=termWidth n := by
  induction n using Nat.strong_induction_on generalizing off with
  | h n ih =>
    rw [emitTerm,termWidth]
    by_cases h0 : n%8=0
    · simp [h0]
    · by_cases h2 : n%8=2
      · have l := ih (n/8).unpair.1 (termChildDecrease _ _ (by simp [childTerm,h2])) off
        have r := ih (n/8).unpair.2 (termChildDecrease _ _ (by simp [childTerm,h2]))
          (off+termWidth (n/8).unpair.1)
        simp [h0,h2,l,r]
      · by_cases h4 : n%8=4
        · have r := ih (n/8).unpair.2 (termChildDecrease _ _ (by simp [childTerm,h2,h4])) off
          simp [h0,h2,h4,r]
        · by_cases h3 : n%8=3 <;> simp [h0,h2,h4,h3]

theorem exactFormulaWidth (off n : Nat) : (emitFormula off n).2.1=formulaWidth n := by
  induction n using Nat.strong_induction_on generalizing off with
  | h n ih =>
    rw [emitFormula,formulaWidth]
    by_cases h : 5≤n%8
    · by_cases h5 : n%8=5
      · have e := ih (n/8) (formulaChildDecrease _ _ (by simp [childFormula,h,h5])) off
        simp [h,h5,e]
      · have e := ih (n/8).unpair.1 (formulaChildDecrease _ _ (by simp [childFormula,h,h5])) off
        have ez := ih (n/8).unpair.2 (formulaChildDecrease _ _ (by simp [childFormula,h,h5]))
          (off+formulaWidth (n/8).unpair.1)
        simp [h,h5,e,ez]
    · by_cases h2 : 2≤n%8 <;> simp [h,h2,exactTermWidth]

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.MatrixCode
