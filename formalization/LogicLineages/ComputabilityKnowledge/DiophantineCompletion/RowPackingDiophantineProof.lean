module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.RowPackingSemanticProof
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.RowPackingClosureProof
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherRelationDiophantineProof
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherIndexDiophantineProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.RowPackingDiophantineProof
open Dioph Elementary Cipher RowPacking RowPackingTargets RowPackingClosureProof

private theorem codeOnFunctions {α : Type} (N Q A : (α → Nat) → Nat)
    (hN : DiophFn N) (hQ : DiophFn Q) (hA : DiophFn A) :
    Dioph {v | CipherRelation.Code (N v) (Q v) (A v)} := by
  exact finCompose CipherRelationDiophantineProof.codeDiophantine ![N,Q,A] (by
    intro i
    fin_cases i
    · exact hN
    · exact hQ
    · exact hA)

private theorem constOnFunctions {α : Type} (N Q C A : (α → Nat) → Nat)
    (hN : DiophFn N) (hQ : DiophFn Q) (hC : DiophFn C) (hA : DiophFn A) :
    Dioph {v | CipherRelation.Const (N v) (Q v) (C v) (A v)} := by
  exact finCompose CipherRelationDiophantineProof.constDiophantine ![N,Q,C,A] (by
    intro i
    fin_cases i
    · exact hN
    · exact hQ
    · exact hC
    · exact hA)

private theorem addOnFunctions {α : Type} (A B C : (α → Nat) → Nat)
    (hA : DiophFn A) (hB : DiophFn B) (hC : DiophFn C) :
    Dioph {v | CipherRelation.Add (A v) (B v) (C v)} := by
  exact finCompose CipherRelationDiophantineProof.addDiophantine ![A,B,C] (by
    intro i
    fin_cases i
    · exact hA
    · exact hB
    · exact hC)

private theorem multOnFunctions {α : Type} (N Q A B C : (α → Nat) → Nat)
    (hN : DiophFn N) (hQ : DiophFn Q) (hA : DiophFn A) (hB : DiophFn B) (hC : DiophFn C) :
    Dioph {v | CipherRelation.Mult (N v) (Q v) (A v) (B v) (C v)} := by
  exact finCompose CipherRelationDiophantineProof.multDiophantine ![N,Q,A,B,C] (by
    intro i
    fin_cases i
    · exact hN
    · exact hQ
    · exact hA
    · exact hB
    · exact hC)

private theorem indexOnFunctions {α : Type} (N Q I : (α → Nat) → Nat)
    (hN : DiophFn N) (hQ : DiophFn Q) (hI : DiophFn I) :
    Dioph {v | IsCipherOf (N v) (Q v) id (I v)} := by
  exact finCompose CipherIndexDiophantineProof.indexCipherDiophantine ![N,Q,I] (by
    intro i
    fin_cases i
    · exact hN
    · exact hQ
    · exact hI)

private theorem constraintOnFunctions {α : Type} (n k : Nat)
    (N Q I : (α → Nat) → Nat) (P : Fin n → (α → Nat) → Nat) (W : Fin k → (α → Nat) → Nat)
    (hN : DiophFn N) (hQ : DiophFn Q) (hI : DiophFn I)
    (hP : ∀ a, DiophFn (P a)) (hW : ∀ b, DiophFn (W b))
    (c : Constraint (Option (Fin n)) (Fin k)) :
    Dioph {v | packedConstraint (N v) (Q v) (I v) (fun a => P a v) (fun b => W b v) c} := by
  obtain ⟨o,r⟩ := c
  cases r with
  | constant c =>
      exact constOnFunctions N Q (fun _ => c) (W o) hN hQ (Dioph.const_dioph c) (hW o)
  | «variable» b => exact Dioph.eq_dioph (hW o) (hW b)
  | «parameter» a =>
      cases a with
      | none => exact Dioph.eq_dioph (hW o) hI
      | some a => exact constOnFunctions N Q (P a) (W o) hN hQ (hP a) (hW o)
  | add b d => exact addOnFunctions (W o) (W b) (W d) (hW o) (hW b) (hW d)
  | mul b d => exact multOnFunctions N Q (W o) (W b) (W d) hN hQ (hW o) (hW b) (hW d)

theorem pointwiseElementaryDiophantine : PointwiseElementaryDiophantine := by
  intro n k m C
  let α := Option (Fin n) ⊕ (Fin k ⊕ Bool)
  let N : (α → Nat) → Nat := fun v => v (.inl none)
  let Q : (α → Nat) → Nat := fun v => v (.inr (.inr false))
  let I : (α → Nat) → Nat := fun v => v (.inr (.inr true))
  let P : Fin n → (α → Nat) → Nat := fun a v => v (.inl (some a))
  let W : Fin k → (α → Nat) → Nat := fun b v => v (.inr (.inl b))
  have hN : DiophFn N := Dioph.proj_dioph _
  have hQ : DiophFn Q := Dioph.proj_dioph _
  have hI : DiophFn I := Dioph.proj_dioph _
  have hP (a : Fin n) : DiophFn (P a) := Dioph.proj_dioph _
  have hW (b : Fin k) : DiophFn (W b) := Dioph.proj_dioph _
  have hi := indexOnFunctions N Q I hN hQ hI
  have hv := finiteForall (fun b : Fin k => {v : α → Nat | CipherRelation.Code (N v) (Q v) (W b v)})
    (fun b => codeOnFunctions N Q (W b) hN hQ (hW b))
  have hc := finiteForall (fun j : Fin m => {v : α → Nat |
      packedConstraint (N v) (Q v) (I v) (fun a => P a v) (fun b => W b v) (C j)})
    (fun j => constraintOnFunctions n k N Q I P W hN hQ hI hP hW (C j))
  have hs : Dioph {v : α → Nat |
      packedSystem C (N v) (Q v) (I v) (fun a => P a v) (fun b => W b v)} := hi.inter (hv.inter hc)
  have hex := Dioph.ex_dioph hs
  apply hex.ext
  intro v
  change (∃ w : Fin k ⊕ Bool → Nat,
    packedSystem C (v none) (w (.inr false)) (w (.inr true)) (fun a => v (some a)) (fun b => w (.inl b))) ↔
      pointwise C (v none) (fun a => v (some a))
  rw [RowPackingSemanticProof.variableRowPacking]
  constructor
  · rintro ⟨w,hw⟩
    exact ⟨w (.inr false),w (.inr true),(fun b => w (.inl b)),hw⟩
  · rintro ⟨q,I,codes,h⟩
    exact ⟨Sum.elim codes (fun b => if b then I else q),h⟩

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.RowPackingDiophantineProof
