module
public import LogicLineages.OrdinalComparison.WWGroundClosingDefinitions
public import LogicLineages.OrdinalComparison.WWDefaultPolicyDefinitions
public import LogicLineages.OrdinalComparison.WWEncodedScalarTargets
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentDefinitions
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxVectorCompilerDefinitions
public import LogicLineages.OrdinalComparison.WWScalarSyntaxCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AbsoluteObserver
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open ForwardTranslation

def groundType {Γ : List Ty} (hΓ : ∀ σ ∈ Γ, σ = Ty.ground)
    {σ : Ty} (x : Variable Γ σ) : σ = Ty.ground := by
  have mem : ∀ {Δ : List Ty} {τ : Ty}, Variable Δ τ → τ ∈ Δ := by
    intro Δ τ y
    induction y with
    | here => exact List.mem_cons_self
    | there y ih => exact List.mem_cons_of_mem _ ih
  exact hΓ σ (mem x)

/-- Close precisely the original ground names, at source syntax level. -/
def closingMap {Γ : List Ty} (hΓ : ∀ σ ∈ Γ, σ = Ty.ground) : GroundClosing.GroundMap Γ [] :=
  fun x => by
    have h := groundType hΓ x
    subst h
    exact .zero

def close {Γ τ} (hΓ : ∀ σ ∈ Γ, σ = Ty.ground) (t : OriginalTerm Γ τ) : OriginalTerm [] τ :=
  t.substitute (GroundClosing.GroundMap.source (closingMap hΓ))

/-- Finite executable compiler output; the target proves both rejecting
branches unreachable on every supplied source. No closed evaluator oracle. -/
def anchorCode {Γ τ} (hΓ : ∀ σ ∈ Γ, σ = Ty.ground) (t : OriginalTerm Γ τ) : Nat :=
  match AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (close hΓ t) with
  | none => 0
  | some w => match compileScalar (w 0) with
    | none => 0
    | some s => scalarCode (fun _ => 0) s

noncomputable def anchor {Γ τ} (hΓ : ∀ σ ∈ Γ, σ = Ty.ground) (t : OriginalTerm Γ τ) : Nat :=
  encodedScalarValue (anchorCode hΓ t) []

/-- Uniform numeric evaluator from an encoded closed original source; failed
raw inputs totalize to zero, but AnchorCorrect proves success on supplied T*. -/
noncomputable def closedSourceValue (n : Nat) : Nat :=
  (((DefaultSourceAssignment.assignmentCode [] n).bind OrdinalSyntax.compileVectorCode).map
    (fun c => scalarSyntaxValue c.1 [])).getD 0

/-- Effective open-source anchor evaluation. The numeric input gives the
number of ground free names and the unchanged source code. The empty numeric
tuple evaluates every ground input at raw one, exactly literal zero closing. -/
noncomputable def openSourceValue (p : Nat × Nat) : Nat :=
  (((DefaultSourceAssignment.assignmentCode
      (List.replicate p.1 (SyntaxCode.typeCode Ty.ground)) p.2).bind OrdinalSyntax.compileVectorCode).map
    (fun c => scalarSyntaxValue c.1 [])).getD 0

def shiftTwo (Γ : List Ty) : Renaming Γ (.ground :: .ground :: Γ) :=
  fun x => .there (.there x)

def fromEmpty (Γ : List Ty) : Renaming [] Γ := fun x => nomatch x

/-- Actual unused ground binder followed by its genuine application, then an
actual unused output-type eraser. Neither application is beta-reduced. -/
def probe {Γ τ} (t : OriginalTerm Γ τ) (x : Variable Γ .ground) : OriginalTerm Γ .ground :=
  .app (.lam .zeroC) (.app (.lam (t.rename (Renaming.weaken Γ .ground))) (.var x))

def originalProbe {Γ τ} (t : OriginalTerm Γ τ) : OriginalTerm (.ground :: .ground :: Γ) .ground :=
  probe (t.rename (shiftTwo Γ)) .here

def closedProbe {Γ τ} (hΓ : ∀ σ ∈ Γ, σ = Ty.ground) (t : OriginalTerm Γ τ) :
    OriginalTerm (.ground :: .ground :: Γ) .ground :=
  probe ((close hΓ t).rename (fromEmpty _)) (.there .here)

/-- Old names share their original valuation; only x,y are fresh. -/
def extend {Γ} (ρ : OrdinalComponent Γ → Nat) (x y : Nat) :
    OrdinalComponent (.ground :: .ground :: Γ) → Nat
  | ⟨_, .here, _⟩ => x
  | ⟨_, .there .here, _⟩ => y
  | ⟨σ, .there (.there z), i⟩ => ρ ⟨σ, z, i⟩

def Observation {Γ} (ρ : OrdinalComponent Γ → Nat) (t : OriginalTerm Γ .ground) (q : Nat) : Prop :=
  ∃ w : OrdinalVector Γ 0,
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t = some w ∧
    denote (fun c => ((ρ c + 1 : Nat) : Ordinal)) (w 0) = ((q + 1 : Nat) : Ordinal)

def factor (τ : Ty) : Nat := 2 * (τ.level + 1) + 1

/-- Existential ground-source observations, addition and fixed constants only.
Products here are multiplication by the fixed source-type numeral factor τ,
not multiplication of arithmetic inputs. v is the raw scalar, x/y/q are
natural encodings of positive raw source values. -/
def Formula {Γ τ} (hΓ : ∀ σ ∈ Γ, σ = Ty.ground)
    (t : OriginalTerm Γ τ) (ρ : OrdinalComponent Γ → Nat) (v : Nat) : Prop :=
  ∃ x y q : Nat,
    Observation (extend ρ x y) (originalProbe t) q ∧
    Observation (extend ρ x y) (closedProbe hΓ t) q ∧
    factor τ * v + (x + 1) = factor τ * anchor hΓ t + (y + 1)
end LogicLineages.OrdinalComparison.Source.AbsoluteObserver
