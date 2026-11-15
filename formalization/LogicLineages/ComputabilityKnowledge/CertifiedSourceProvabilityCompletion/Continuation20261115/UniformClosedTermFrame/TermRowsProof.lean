module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.EntriesConsProof
public import Mathlib.Tactic.FinCases
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.TermRowsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph EntriesLogic
open RelationalSyntaxDepthTransport ConstructorStepTargets
open UniformFixedFormulaAgreement.StackProof
/-- Every non-variable original term row retains only term tasks at the same
bound. This finite statement is not arbitrary runtime-token classification. -/
theorem rowEntries {ctx : Nat} (ptag : Nat) (i : Fin 6) (hi : i ≠ 0) :
 ∀ x ∈ tasks ptag (.zero : Term ctx) (.term i), x = LiteralSyntaxStep.taskCall ptag 0 .zero := by
 fin_cases i
 · exact (hi rfl).elim
 all_goals simp only [tasks, List.mem_cons, List.not_mem_nil, or_false]
 all_goals intro x hx; rcases hx with rfl | rfl <;> rfl

theorem prependEntries {n ctx : Nat} (p : Program n) (q ctag : Nat)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (value : Term ctx) (xs : List (Term ctx)) (rest : Term ctx)
 (hx : ∀ x ∈ xs, x = value) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (entries q value rest) (entries q value (prepend ctag xs rest)))) := by
 induction xs with
 | nil =>
  have h : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx [entries q value rest] (entries q value rest) :=
   .hypothesis List.mem_cons_self
  exact ⟨h.discharge.finish⟩
 | cons x xs ih =>
  have he := hx x List.mem_cons_self
  subst x
  obtain ⟨ht⟩ := ih (fun y hy => hx y (List.mem_cons_of_mem _ hy))
  obtain ⟨hcns⟩ := EntriesConsProof.cons p q ctag hq hc value (prepend ctag xs rest)
  have h : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx [entries q value rest] (entries q value rest) :=
   .hypothesis List.mem_cons_self
  exact ⟨(Hilbert.Local.mp (.base hcns) (.mp (.base ht) h)).discharge.finish⟩

theorem outputEntries {n ctx : Nat} (p : Program n) (q ptag ctag atag : Nat)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (i : Fin 6) (hi : i ≠ 0) (rest : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (entries q (LiteralSyntaxStep.taskCall ptag 0 .zero) rest)
   (entries q (LiteralSyntaxStep.taskCall ptag 0 .zero) (output ptag ctag atag (.term i) .zero rest)))) := by
 let value : Term ctx := LiteralSyntaxStep.taskCall ptag 0 .zero
 obtain ⟨he⟩ := prependEntries p q ctag hq hc value (tasks ptag .zero (.term i)) rest (rowEntries ptag i hi)
 obtain ⟨hp⟩ := appendPrefix p ctag atag hc ha (tasks ptag .zero (.term i)) rest
 let H := entries q value rest
 have hh : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx [H] H := .hypothesis List.mem_cons_self
 have hpre := Hilbert.Local.mp (.base he) hh
 have hout := Hilbert.Local.mp (.mp (.base (transportTasks q value
  (prepend ctag (tasks ptag .zero (.term i)) rest) (output ptag ctag atag (.term i) .zero rest)))
  (.base (Support.equalitySymmetry _ _ hp))) hpre
 exact ⟨hout.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.TermRowsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.TermRowsProof
