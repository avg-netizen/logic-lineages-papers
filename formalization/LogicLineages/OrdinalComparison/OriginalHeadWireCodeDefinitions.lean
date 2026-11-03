module
public import LogicLineages.OrdinalComparison.PaidHeadTransportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.OriginalHeadWireCode
open Arithmetic ArithmeticCode OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def first (σ : Ty) (h : 0<σ.level) : Fin (σ.level+1) := ⟨1,by omega⟩
def functionFirst (σ τ : Ty) : Fin (Ty.arrow σ τ).level.succ :=
  ⟨1,by have h := Nat.le_max_left (σ.level+1) τ.level; change 1<max (σ.level+1) τ.level+1; omega⟩
def boxSecond (σ τ : Ty) (hσ : 0<σ.level) : Fin (Ty.arrow σ τ).level.succ :=
  ⟨2,by have h := Nat.le_max_left (σ.level+1) τ.level; change 2<max (σ.level+1) τ.level+1; omega⟩

noncomputable def originalPaidValue {Γ : List Ty} (σ τ : Ty) (hσ : 0<σ.level) (b : Nat)
    (B : OrdinalVector Γ (Ty.arrow σ τ).level) (C : OrdinalVector Γ σ.level) : Ordinal :=
  ordinalNaturalProduct ((2^b : Nat) : Ordinal)
    (ordinalNaturalSum (denote (fun _ => 1) (B (functionFirst σ τ)))
      (denote (fun _ => 1) (C (first σ hσ))))

noncomputable def scalarValue {Γ : List Ty} {m : Nat} (u : OrdinalVector Γ m)
    (ρ : Variable Γ .ground → Nat) := finiteValue (expressionValue (UnitObservation.substitution ρ) (u 0))
noncomputable def originalWire {Γ : List Ty} {m n : Nat} (ξ : Ordinal) (level : Nat)
    (B : OrdinalVector Γ m) (C : OrdinalVector Γ n) (ρ : Variable Γ .ground → Nat) :=
  actualOrdinalNorm ξ + scalarValue B ρ + scalarValue C ρ + level

def wireExpr (norm level : Nat) : Expr :=
  .add (.add (.add (.numeral norm) (.variable 1)) (.variable 0)) (.numeral level)
def wireCode (norm level : Nat) :=
  addCode (addCode (addCode (numeralCode norm) (variableCode 1)) (variableCode 0)) (numeralCode level)
def combine (fB fC fG : Formula) : Formula := .existsNat (.existsNat (conjunction [fB,fC,fG]))
def combineCode (fB fC fG : Nat) := existsCode (existsCode (conjunctionCode [fB,fC,fG]))

/-- Actual original source application typing is checked; source scalar
observation preserves Γ and shared input expressions, with no ground closure. -/
noncomputable def compileCode (Γ : List Nat) (B C : Nat) (Θ : List Nat) (K δ : Nat)
    (xs : List Nat) (y : Nat) : Option Nat := do
  let σ ← SyntaxCode.check Γ C
  let arrow ← SyntaxCode.check Γ B
  if arrow ≠ 0 ∧ (arrow-1).unpair.1=σ ∧ 0<SyntaxCode.typeLevel σ then
    let p ← GraphCode.constantsCode Θ K
    let fB ← UnitArithmeticFormulaCode.sourceFormulaCode Γ B
      (xs.map (liftCode 2)) (variableCode 1)
    let fC ← UnitArithmeticFormulaCode.sourceFormulaCode Γ C
      (xs.map (liftCode 2)) (variableCode 0)
    let fG := GraphCode.graphCode Θ.length p.1 p.2.1 δ p.2.2
      (wireCode (GraphCode.shiftedNormCode p.1 δ) (SyntaxCode.typeLevel σ)) (liftCode 2 y)
    pure (combineCode fB fC fG)
  else none
abbrev RawInput := List Nat×Nat×Nat×List Nat×Nat×Nat×List Nat×Nat
end LogicLineages.OrdinalComparison.Source.ActualHeadGraph.OriginalHeadWireCode
