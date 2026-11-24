module

public import LogicLineages.PersistentMarking.NumberedWindowScalarAlgorithm
public import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxGuardNumericProof
open NumberedWindowFieldAlgorithm (pack packNode unpackNode)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)

private theorem pairBounds (a b : Nat) : a ≤ pair a b ∧ b ≤ pair a b := by
  let s := a+b
  have hs : s ≤ s*s := by
    by_cases z : s = 0
    · rw [z]
      exact Nat.zero_le _
    · have one : 1 ≤ s := Nat.pos_of_ne_zero z
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left s one
  have h := Nat.le_trans hs (Nat.le_add_right (s*s) a)
  exact ⟨Nat.le_trans (Nat.le_add_right a b) h,Nat.le_trans (Nat.le_add_left b a) h⟩

private theorem packBelow (xs : List Nat) (w : Nat) (h : w ∈ xs) : w < pack xs := by
  induction xs with
  | nil => cases h
  | cons a xs ih =>
    rcases List.mem_cons.mp h with rfl | tail
    · exact Nat.lt_succ_of_le (pairBounds w (pack xs)).1
    · exact Nat.lt_succ_of_le (Nat.le_trans (Nat.le_of_lt (ih tail)) (pairBounds a (pack xs)).2)

theorem fieldBelow {n tag x : Nat} {row : List Nat}
    (parsed : unpackNode n = some (tag,row)) (selected : x ∈ row) : x < n := by
  rw [codeOfNode parsed]
  exact Nat.lt_succ_of_le (Nat.le_trans (Nat.le_of_lt (packBelow row x selected))
    (pairBounds tag (pack row)).2)

theorem previous {A : Type} (table : Nat → List A) (result : Nat → A)
    (start : table 0 = []) (next : ∀ n, table (n+1) = table n ++ [result n])
    {i n : Nat} (below : i < n) : (table n)[i]? = some (result i) := by
  have length : ∀ n, (table n).length = n := by
    intro j
    induction j with
    | zero => simp [start]
    | succ j ih => simp [next,ih]
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : i < n
    · have index : i < (table n).length := by rw [length n]; exact h
      rw [next,List.getElem?_append_left index]
      exact ih h
    · have same : i = n := by omega
      subst i
      rw [next]
      simpa only [length] using (List.getElem?_concat_length (l := table n) (a := result n))

section Syntax
open NumberedWindowSyntaxAlgorithm

theorem exact_AuxSyntaxChildren (q d c fn arg : Nat) (parsed : unpackNode q = some (6,[d,c,fn,arg]))
    (held : (syntaxBits q).1 = true) :
    (syntaxBits fn).1 = true ∧ (syntaxBits arg).1 = true := by
  have f := previous table syntaxBits rfl (fun _ => rfl) (fieldBelow parsed (by simp : fn ∈ [d,c,fn,arg]))
  have a := previous table syntaxBits rfl (fun _ => rfl) (fieldBelow parsed (by simp : arg ∈ [d,c,fn,arg]))
  change termNext q (table q) = true at held
  simp only [termNext,parsed,Option.any,termParts,List.getD_eq_getElem?_getD,f,a,Option.getD_some,Bool.and_eq_true] at held
  exact ⟨held.1.2,held.2⟩
end Syntax

section Lexical
open NumberedWindowLexicalAlgorithm
open NumberedWindowAnnotationAlgorithm (annotations arrow)

theorem exact_AuxTypedChildren (ctx : List Nat) (ty q d c fn arg : Nat)
    (parsed : unpackNode q = some (6,[d,c,fn,arg])) (held : typed ctx ty q = true) :
    typed ctx (arrow d c) fn = true ∧ typed ctx d arg = true := by
  have f := previous table requirements rfl (fun _ => rfl) (fieldBelow parsed (by simp : fn ∈ [d,c,fn,arg]))
  have a := previous table requirements rfl (fun _ => rfl) (fieldBelow parsed (by simp : arg ∈ [d,c,fn,arg]))
  have syn := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp held).1).1
  obtain ⟨sf,sa⟩ := exact_AuxSyntaxChildren q d c fn arg parsed syn
  have req : holds (fun i => ctx[i]?) (requirements q).1 = true :=
    (Bool.and_eq_true_iff.mp held).2
  change holds (fun i => ctx[i]?) (termNext q (table q)) = true at req
  rw [termNext,parsed] at req
  change holds (fun i => ctx[i]?)
    (join (restrict ((annotations fn).1 == arrow d c) ((table q).getD fn default).1)
          (restrict ((annotations arg).1 == d) ((table q).getD arg default).1)) = true at req
  simp only [List.getD_eq_getElem?_getD,f,a,Option.getD_some,holds,join,restrict,
    List.all_append,Bool.and_eq_true] at req
  have lf : holds (fun i => ctx[i]?) (requirements fn).1 = true := by
    simp only [holds,Bool.and_eq_true]
    exact ⟨req.1.1.2,req.2.1⟩
  have la : holds (fun i => ctx[i]?) (requirements arg).1 = true := by
    simp only [holds,Bool.and_eq_true]
    exact ⟨req.1.2.2,req.2.2⟩
  have bf := req.1.1.1
  have ba := req.1.2.1
  exact ⟨by simp only [typed,sf,bf,lf]; rfl,by simp only [typed,sa,ba,la]; rfl⟩

end Lexical

section Admission
open NumberedWindowAdmissionAlgorithm

theorem exact_AuxAdmissionChildren (window : Window) (q d c fn arg : Nat)
    (parsed : unpackNode q = some (6,[d,c,fn,arg])) (held : (bits window q).1 = true) :
    (bits window fn).1 = true ∧ (bits window arg).1 = true := by
  have f := previous (table window) (rawBits window) rfl (fun _ => rfl)
    (fieldBelow parsed (by simp : fn ∈ [d,c,fn,arg]))
  have a := previous (table window) (rawBits window) rfl (fun _ => rfl)
    (fieldBelow parsed (by simp : arg ∈ [d,c,fn,arg]))
  have syn := (Bool.and_eq_true_iff.mp held).1
  obtain ⟨sf,sa⟩ := exact_AuxSyntaxChildren q d c fn arg parsed syn
  have adm := (Bool.and_eq_true_iff.mp held).2
  change termNext window q (table window q) = true at adm
  rw [termNext,parsed] at adm
  change ((window.1.contains c && window.1.contains d) &&
    ((table window q).getD fn (false,false)).1 && ((table window q).getD arg (false,false)).1) = true at adm
  simp only [List.getD_eq_getElem?_getD,f,a,Option.getD_some,Bool.and_eq_true] at adm
  exact ⟨by simp [bits,sf,adm.1.2],by simp [bits,sa,adm.2]⟩
end Admission

/-- Exact numerical window observations in the same original lexical
context, from successful admission of an arbitrary raw auxiliary code. -/
theorem exact_AuxAdmittedChildren (s : NumberedWindowScalarAlgorithm.Settings)
    (ctx : List Nat) (ty q d c fn arg : Nat) (parsed : unpackNode q = some (6,[d,c,fn,arg]))
    (held : NumberedWindowScalarAlgorithm.admitted s ctx ty q = true) :
    NumberedWindowScalarAlgorithm.admitted s ctx (NumberedWindowAnnotationAlgorithm.arrow d c) fn = true ∧
    NumberedWindowScalarAlgorithm.admitted s ctx d arg = true := by
  obtain ⟨typ,seen⟩ := Bool.and_eq_true_iff.mp held
  obtain ⟨t1,t2⟩ := exact_AuxTypedChildren ctx ty q d c fn arg parsed typ
  obtain ⟨a1,a2⟩ := exact_AuxAdmissionChildren s.window q d c fn arg parsed seen
  exact ⟨by simp [NumberedWindowScalarAlgorithm.admitted,t1,a1],
    by simp [NumberedWindowScalarAlgorithm.admitted,t2,a2]⟩

#print axioms exact_AuxSyntaxChildren
#print axioms exact_AuxTypedChildren
#print axioms exact_AuxAdmissionChildren
#print axioms exact_AuxAdmittedChildren
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxGuardNumericProof
