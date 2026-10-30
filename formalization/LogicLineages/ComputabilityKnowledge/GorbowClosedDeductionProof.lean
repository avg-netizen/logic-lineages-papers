module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowClosedDeduction
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryProofProof
public import LogicLineages.ComputabilityKnowledge.GorbowFormulaCompositionProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowClosedDeductionProof
open GorbowSyntax GorbowTheoryProof GorbowClosedDeduction GorbowPACore GorbowFormulaSubstitution

private theorem liftVariables (n : Nat) : liftSubstitute (Term.var : Fin n → Term n)=Term.var := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => rfl

private theorem formulaVariables {n : Nat} (φ : Formula n) : substituteFormula Term.var φ=φ := by
  induction φ with
  | equal t u | knowledge t u => simp only [substituteFormula,GorbowSubstitution.substitute_variables]
  | universalRelation t | agent t | knowledgeAll t | truth t => simp only [substituteFormula,GorbowSubstitution.substitute_variables]
  | neg φ ih => simp only [substituteFormula,ih]
  | imp φ ψ hφ hψ | conj φ ψ hφ hψ | disj φ ψ hφ hψ => simp only [substituteFormula,hφ,hψ]
  | all φ ih | ex φ ih => simp only [substituteFormula,liftVariables,ih]

theorem closedSyntax : Comparators.GorbowClosedDeduction.ClosedSyntax := by
  constructor
  · intro R
    have h : (Fin.elim0 : Fin 0 → Term 0)=Term.var := by funext i; exact Fin.elim0 i
    simpa only [weakenClosed,h] using formulaVariables R
  · intro n R
    unfold weaken weakenClosed
    rw [GorbowFormulaCompositionProof.composition]
    congr 1
    funext i
    exact Fin.elim0 i

private def implicationIdentity (A : Sentence → Prop) {n : Nat} (a : Formula n) : Derivation A (.imp a a) :=
  .mp (.mp (.logical (.s a (.imp a a) a)) (.logical (.k a (.imp a a)))) (.logical (.k a a))

private def liftProof {A : Sentence → Prop} {n : Nat} {a : Formula n} (r : Formula n)
    (p : Derivation A a) : Derivation A (.imp r a) := .mp (.logical (.k a r)) p

private def compose {A : Sentence → Prop} {n : Nat} {a b c : Formula n}
    (p : Derivation A (.imp b c)) (q : Derivation A (.imp a b)) : Derivation A (.imp a c) :=
  .mp (.mp (.logical (.s a b c)) (liftProof a p)) q

theorem deduction : Comparators.GorbowClosedDeduction.Deduction := by
  intro A R n φ p
  induction p with
  | logical w => exact ⟨liftProof _ (.logical w)⟩
  | arithmetic w => exact ⟨liftProof _ (.arithmetic w)⟩
  | «axiom» σ h =>
    rcases h with h | rfl
    · exact ⟨liftProof _ (.axiom σ h)⟩
    · exact ⟨implicationIdentity A _⟩
  | @mp n a b p q hp hq =>
    obtain ⟨pp⟩ := hp
    obtain ⟨qq⟩ := hq
    exact ⟨.mp (.mp (.logical (.s (weakenClosed n R) a b)) pp) qq⟩
  | @generalize n a p hp =>
    obtain ⟨pp⟩ := hp
    have hd : Derivation A (.imp (.all (weakenClosed (n+1) R)) (.all a)) :=
      .mp (.logical (.allDistribute (weakenClosed (n+1) R) a)) (.generalize pp)
    have hv : Derivation A (.imp (weakenClosed n R) (.all (weakenClosed (n+1) R))) := by
      simpa only [logicalFormula,closedSyntax.2] using (Derivation.logical (A:=A) (.allVacuous (weakenClosed n R)))
    exact ⟨compose hd hv⟩

theorem discharge : Comparators.GorbowClosedDeduction.Discharge := by
  intro A R n φ p
  have hp := GorbowTheoryProofProof.monotonicity A (extend A R) (fun _ h => Or.inl h) n _ ⟨p⟩
  obtain ⟨q⟩ := hp
  exact ⟨.mp q (.axiom R (Or.inr rfl))⟩

theorem exactExtension : Comparators.GorbowClosedDeduction.ExactExtension := by
  intro A R n φ
  constructor
  · rintro ⟨p⟩; exact deduction A R n φ p
  · rintro ⟨p⟩; exact discharge A R n φ p

theorem closedExtension : Comparators.GorbowClosedDeduction.ClosedExtension := by
  intro A R σ
  simpa only [closedSyntax.1] using exactExtension A R 0 σ

theorem gorbowClosedDeduction : Comparators.GorbowClosedDeduction.Target :=
  ⟨closedSyntax,deduction,discharge,exactExtension,closedExtension⟩
end LogicLineages.ComputabilityKnowledge.GorbowClosedDeductionProof
