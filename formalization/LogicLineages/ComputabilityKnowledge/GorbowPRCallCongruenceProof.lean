module

public import LogicLineages.ComputabilityKnowledge.GorbowPRCallCongruenceTargets
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryEqualityProof
public import LogicLineages.ComputabilityKnowledge.GorbowHeaderSubstitutionProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPRCallCongruence.Proof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowClosedEquality
open GorbowPRDefiningEquations

private theorem subLift (t x : Term 0) :
    substitute (Fin.cases x Fin.elim0) (liftClosedTerm 1 t) = t :=
  GorbowClosedEqualityProof.closedTransport 1 t _

private theorem addCongruence (A : Sentence → Prop) (a b a' b' : Term 0)
    (p : Derivation A (.equal a a')) (q : Derivation A (.equal b b')) :
    Nonempty (Derivation A (.equal (.add a b) (.add a' b'))) := by
  have h1 := GorbowTheoryEqualityProof.termCongruence A
    (.add (.var 0) (liftClosedTerm 1 b)) a a' p
  have h2 := GorbowTheoryEqualityProof.termCongruence A
    (.add (liftClosedTerm 1 a') (.var 0)) b b' q
  simp only [instantiateTerm, substitute, Fin.cases_zero, subLift] at h1 h2
  obtain ⟨p1⟩ := h1
  obtain ⟨p2⟩ := h2
  exact GorbowTheoryEqualityProof.transitivity A _ _ _ p1 p2

private theorem mulCongruence (A : Sentence → Prop) (a b a' b' : Term 0)
    (p : Derivation A (.equal a a')) (q : Derivation A (.equal b b')) :
    Nonempty (Derivation A (.equal (.mul a b) (.mul a' b'))) := by
  have h1 := GorbowTheoryEqualityProof.termCongruence A
    (.mul (.var 0) (liftClosedTerm 1 b)) a a' p
  have h2 := GorbowTheoryEqualityProof.termCongruence A
    (.mul (liftClosedTerm 1 a') (.var 0)) b b' q
  simp only [instantiateTerm, substitute, Fin.cases_zero, subLift] at h1 h2
  obtain ⟨p1⟩ := h1
  obtain ⟨p2⟩ := h2
  exact GorbowTheoryEqualityProof.transitivity A _ _ _ p1 p2

theorem termCongruence : Targets.TermCongruence := by
  intro A n t sigma tau h
  induction t with
  | var i => exact h i
  | zero => exact ⟨.logical (.reflexive .zero)⟩
  | succ t ih =>
      obtain ⟨p⟩ := ih
      simpa only [instantiateTerm, substitute, Fin.cases_zero] using
        GorbowTheoryEqualityProof.termCongruence A (.succ (.var 0)) _ _ p
  | add t u ht hu =>
      obtain ⟨p⟩ := ht
      obtain ⟨q⟩ := hu
      exact addCongruence A _ _ _ _ p q
  | mul t u ht hu =>
      obtain ⟨p⟩ := ht
      obtain ⟨q⟩ := hu
      exact mulCongruence A _ _ _ _ p q
  | universalFunction t ih =>
      obtain ⟨p⟩ := ih
      simpa only [instantiateTerm, substitute, Fin.cases_zero] using
        GorbowTheoryEqualityProof.termCongruence A (.universalFunction (.var 0)) _ _ p

theorem callSubstitution : Targets.CallSubstitution := by
  intro ctx out arity tag args sigma
  unfold call
  rw [substitute, GorbowHeaderSubstitutionProof.headers]
  rfl

private theorem argumentSubstitution {arity : Nat} (args : List.Vector (Term 0) arity) :
    (argumentVariables arity).map (substitute args.get) = args := by
  apply List.Vector.ext
  intro i
  simp [argumentVariables, substitute]

theorem callCongruence : Targets.CallCongruence := by
  intro A arity tag args others h
  have ht := termCongruence A arity (call tag (argumentVariables arity)) args.get others.get h
  rw [callSubstitution, callSubstitution, argumentSubstitution, argumentSubstitution] at ht
  exact ht

end LogicLineages.ComputabilityKnowledge.GorbowPRCallCongruence.Proof
