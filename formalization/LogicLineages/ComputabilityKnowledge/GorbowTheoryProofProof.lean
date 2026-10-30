module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowTheoryProof
public import LogicLineages.ComputabilityKnowledge.GorbowPACoreProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowTheoryProofProof
open GorbowSyntax GorbowTheoryProof

theorem weakeningSemantics : Comparators.GorbowTheoryProof.WeakeningSemantics := by
  intro n σ I v
  have h := GorbowFormulaSubstitution.substituteFormula_realize σ I v (Fin.elim0 : Fin 0 → Term n)
  have he : (fun i : Fin 0 => (Fin.elim0 i : Term n).realize I v)=Fin.elim0 := by
    funext i; exact Fin.elim0 i
  simpa only [weakenClosed,he] using h

theorem usedMembership : Comparators.GorbowTheoryProof.UsedMembership := by
  intro A n φ p
  induction p with
  | logical w => simp [usedAxioms]
  | arithmetic w => simp [usedAxioms]
  | «axiom» σ h => simpa [usedAxioms] using h
  | mp p q hp hq =>
    intro σ hs
    rcases List.mem_append.mp hs with hs | hs
    · exact hp σ hs
    · exact hq σ hs
  | generalize p hp => exact hp

def rebaseTree {A B : Sentence → Prop} {n : Nat} {φ : Formula n} (p : Derivation A φ)
    (h : ∀ σ ∈ usedAxioms p, B σ) : Derivation B φ :=
  match p with
  | .logical w => .logical w
  | .arithmetic w => .arithmetic w
  | .axiom σ _ => .axiom σ (h σ (by simp [usedAxioms]))
  | .mp p q => .mp (rebaseTree p (fun σ hs => h σ (List.mem_append_left _ hs)))
      (rebaseTree q (fun σ hs => h σ (List.mem_append_right _ hs)))
  | .generalize p => .generalize (rebaseTree p h)

theorem rebase : Comparators.GorbowTheoryProof.Rebase :=
  fun _ _ _ _ p h => ⟨rebaseTree p h⟩

theorem monotonicity : Comparators.GorbowTheoryProof.Monotonicity := by
  intro A B h n φ hp
  obtain ⟨p⟩ := hp
  exact rebase A B n φ p (fun σ hs => h σ (usedMembership A n φ p σ hs))

theorem finiteRestriction : Comparators.GorbowTheoryProof.FiniteRestriction :=
  fun A n φ p => rebase A (fun σ => σ∈usedAxioms p) n φ p (fun _ hs => hs)

def coreTree (A : Sentence → Prop) : {n : Nat} → {φ : Formula n} → GorbowPACore.Proof φ → Derivation A φ
  | _,_,.logical w => .logical w
  | _,_,.arithmetic w => .arithmetic w
  | _,_,.mp p q => .mp (coreTree A p) (coreTree A q)
  | _,_,.generalize p => .generalize (coreTree A p)

theorem coreEmbedding : Comparators.GorbowTheoryProof.CoreEmbedding :=
  fun A _ _ p => ⟨coreTree A p⟩

theorem finiteUseSoundness : Comparators.GorbowTheoryProof.FiniteUseSoundness := by
  intro A n φ p
  induction p with
  | logical w => intro I _ v; exact GorbowPACoreProof.logicalSoundness _ w I v
  | arithmetic w => intro I _ v; exact GorbowPACoreProof.arithmeticSoundness _ w I v
  | «axiom» σ h =>
    intro I hv v
    exact (weakeningSemantics _ σ I v).mpr (hv σ (by simp [usedAxioms]))
  | mp p q hp hq =>
    intro I h v
    exact hp I (fun σ hs => h σ (List.mem_append_left _ hs)) v
      (hq I (fun σ hs => h σ (List.mem_append_right _ hs)) v)
  | generalize p hp => intro I h v x; exact hp I h (Fin.cases x v)

theorem theorySoundness : Comparators.GorbowTheoryProof.TheorySoundness := by
  intro A n φ p I h
  exact finiteUseSoundness A n φ p I (fun σ hs => h σ (usedMembership A n φ p σ hs))

theorem gorbowTheoryProof : Comparators.GorbowTheoryProof.Target :=
  ⟨weakeningSemantics,usedMembership,rebase,monotonicity,finiteRestriction,coreEmbedding,finiteUseSoundness,theorySoundness⟩
end LogicLineages.ComputabilityKnowledge.GorbowTheoryProofProof
