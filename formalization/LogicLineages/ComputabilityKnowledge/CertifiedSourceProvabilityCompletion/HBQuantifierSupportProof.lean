module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.LogicalSupportProof

@[expose] public section
/-! Quantifier bookkeeping for actual internal HB implications. Every proof
uses the original Hilbert rules. In particular, generalization is applied to
an ordinary Derivation, never to an undischarged local assumption. -/
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.HBQuantifier
open GorbowSyntax GorbowTheoryProof

noncomputable def contrapose {T : Sentence → Prop} {n : Nat} {a b : Formula n}
    (h : Derivation T (.imp a b)) : Derivation T (.imp (.neg b) (.neg a)) := by
  have hn : Hilbert.Local T n [.neg b] (.neg a) := Hilbert.Local.classical (.neg a)
    (Hilbert.Local.explosion (.neg a)
      (.mp (.base h) (.mp (.base (Hilbert.doubleNegation a))
        (.hypothesis List.mem_cons_self)))
      (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)))
  exact Hilbert.Local.finish (Hilbert.Local.discharge hn)

theorem existentialMonotonicity (T : Sentence → Prop) {n : Nat}
    (a b : Formula (n+1)) (h : Nonempty (Derivation T (.imp a b))) :
    Nonempty (Derivation T (.imp (.ex a) (.ex b))) := by
  obtain ⟨d⟩ := h
  have hall : Derivation T (.imp (.all (.neg b)) (.all (.neg a))) :=
    .mp (.logical (.allDistribute (.neg b) (.neg a))) (.generalize (contrapose d))
  have hneg := contrapose hall
  exact ⟨Hilbert.compose (.logical (.existsDualBackward b))
    (Hilbert.compose hneg (.logical (.existsDualForward a)))⟩

theorem existentialIntroduction (T : Sentence → Prop) {n : Nat}
    (a : Formula (n+1)) (t : Term n)
    (h : Nonempty (Derivation T (GorbowStandardInstances.instantiate a t))) :
    Nonempty (Derivation T (.ex a)) := by
  obtain ⟨d⟩ := h
  let P := Formula.all (.neg a)
  let A := GorbowStandardInstances.instantiate a t
  have hi : Derivation T (.imp P (.neg A)) := .logical (.allInstantiate (.neg a) t)
  have hp : Hilbert.Local T n [.neg (.neg P)] P :=
    .mp (.base (Hilbert.doubleNegation P)) (.hypothesis List.mem_cons_self)
  have hn : Hilbert.Local T n [] (.neg P) := Hilbert.Local.classical (.neg P)
    (Hilbert.Local.explosion (.neg P) (.base d) (.mp (.base hi) hp))
  exact ⟨.mp (.logical (.existsDualBackward a)) (Hilbert.Local.finish hn)⟩

theorem existentialVacuity (T : Sentence → Prop) {n : Nat} (b : Formula n) :
    Nonempty (Derivation T (.imp (.ex (GorbowPACore.weaken b)) b)) := by
  have hv : Derivation T (.imp (.neg b) (.all (.neg (GorbowPACore.weaken b)))) :=
    .logical (.allVacuous (.neg b))
  have hn := contrapose hv
  exact ⟨Hilbert.compose (Hilbert.doubleNegation b)
    (Hilbert.compose hn (.logical (.existsDualForward (GorbowPACore.weaken b))))⟩

theorem existentialElimination (T : Sentence → Prop) {n : Nat}
    (a : Formula (n+1)) (b : Formula n)
    (h : Nonempty (Derivation T (.imp a (GorbowPACore.weaken b)))) :
    Nonempty (Derivation T (.imp (.ex a) b)) := by
  obtain ⟨hm⟩ := existentialMonotonicity T a (GorbowPACore.weaken b) h
  obtain ⟨hv⟩ := existentialVacuity T b
  exact ⟨Hilbert.compose hv hm⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.HBQuantifier
