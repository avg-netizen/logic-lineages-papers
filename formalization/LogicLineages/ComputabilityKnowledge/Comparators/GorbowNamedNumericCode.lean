module

public import LogicLineages.ComputabilityKnowledge.GorbowNamedNumericCode
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowNamedNumericCode
open GorbowSyntax GorbowFreeSupport GorbowNamedBinding GorbowCodeConstructors
open LogicLineages.ComputabilityKnowledge.GorbowNamedNumericCode

def ExactInput : Prop := ∀ v code raw, namedInput v code=some raw ↔
  ∃ (n : Nat) (φ : Formula n) (hv : v<n),
    code=formulaNumber φ ∧ formulaSupport φ={v} ∧ raw=GorbowFormulaPrefixCode.encode φ

def OriginalCalibration : Prop := ∀ n (φ : Formula n) (v : Fin n), formulaSupport φ={v.val} →
  namedInput v.val (formulaNumber φ)=some (GorbowFormulaPrefixCode.encode φ) ∧
  allNumber v.val (formulaNumber φ)=some (formulaNumber (bindAll v φ)) ∧
  exNumber v.val (formulaNumber φ)=some (formulaNumber (bindEx v φ)) ∧
  selectNumber v.val (formulaNumber φ)=some (formulaNumber (selectVariable v φ))

def OutputDomains : Prop := ∀ v code out,
  (allNumber v code=some out → ∃ σ : Sentence, out=formulaNumber σ) ∧
  (exNumber v code=some out → ∃ σ : Sentence, out=formulaNumber σ) ∧
  (selectNumber v code=some out → ∃ A : Selector, out=formulaNumber A.val)

def OriginalSemantics : Prop := ∀ n (φ : Formula n) (v : Fin n), formulaSupport φ={v.val} →
  ∃ (σ τ : Sentence) (A : Selector),
    allNumber v.val (formulaNumber φ)=some (formulaNumber σ) ∧
    exNumber v.val (formulaNumber φ)=some (formulaNumber τ) ∧
    selectNumber v.val (formulaNumber φ)=some (formulaNumber A.val) ∧
    ∀ I ρ, (σ.realize I Fin.elim0 ↔ ∀ x, φ.realize I (assignAt ρ v x)) ∧
      (τ.realize I Fin.elim0 ↔ ∃ x, φ.realize I (assignAt ρ v x)) ∧
      (A.val.realize I (Fin.cases (ρ v) Fin.elim0) ↔ φ.realize I ρ)

def ExactRejection : Prop := ∀ v code,
  (allNumber v code=none ↔ namedInput v code=none) ∧
  (exNumber v code=none ↔ namedInput v code=none) ∧
  (selectNumber v code=none ↔ namedInput v code=none)

def UniformPrograms : Prop :=
  Primrec (fun p : Nat × Nat => namedInput p.1 p.2) ∧
  Primrec (fun p : Nat × Nat => allNumber p.1 p.2) ∧
  Primrec (fun p : Nat × Nat => exNumber p.1 p.2) ∧
  Primrec (fun p : Nat × Nat => selectNumber p.1 p.2)

def Target : Prop := ExactInput ∧ OriginalCalibration ∧ OutputDomains ∧ OriginalSemantics ∧ ExactRejection ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowNamedNumericCode
