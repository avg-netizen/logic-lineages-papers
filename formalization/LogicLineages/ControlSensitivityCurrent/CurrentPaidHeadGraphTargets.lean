module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphCompilerDefinitions
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphFoundationTargets
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphUnitCodeTargets
public import LogicLineages.ControlSensitivityCurrent.CurrentCompilerTargets
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.Targets

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open AdmissibleSum
open CurrentUnitElimination (OpenGraph HoldsRaw oldGround groundCtx groundOnlyContext render)
open PolicyProgramComparisonTargets (Strict Weak)

/-- Actual closed original S, with the correctly encoded raw convention. -/
def ExactS : Prop := ∀ (p : Policy) (f : Nat → Nat), FullAddition.Targets.SourceGrowth f →
  ∀ n : Nat, SourceAST.callValue p f actualS n = f (n+4)

/-- Even finite-prefix inputs outside the auxiliary ray are all admitted,
and non-genuine inputs are excluded. The supporting ray hypothesis is fully
paid from actual K and 437 in ExactNumbered. -/
def ExactDirectTemplate : Prop :=
  ∀ (p : Policy) (f : Nat → Nat), FullAddition.Targets.SourceGrowth f →
  ∀ (β : Ordinal), β < epsilonZero → Order.IsSuccLimit β →
  ∀ (c δ : Nat) (Γ : List Ty) (hg : ∀ σ ∈ Γ, σ = .ground)
    (r : OpenGraph (.ground :: Γ)),
    (∀ (ρ : Variable (.ground :: Γ) .ground → Nat) (v : Nat),
      HoldsRaw p f r ρ v ↔ v = J f β (RayBase β c+ρ .here)) →
    ∀ t y : Nat, (typedDirect hg f β c δ r).holds p f (endValues t y) ↔
      actualOrdinalNorm (shiftHead β δ) ≤ t ∧ y = J f (shiftHead β δ) t

/-- The actual same old input valuation is passed to each observation;
only B/C scalar witnesses and the numerical t splice are new. -/
def ExactInsertedTemplate : Prop :=
  ∀ (p : Policy) (f : Nat → Nat) (Γ : List Ty) (hg : ∀ σ ∈ Γ, σ = .ground)
    (nξ level : Nat) (b c : OpenGraph Γ) (g : Presented DirectCtx)
    (ρ : Variable Γ .ground → Nat) (y : Nat),
    (inserted hg nξ level b c g).holds p f (resultValues ρ y) ↔
      ∃ (B₀ C₀ : Nat), HoldsRaw p f b ρ B₀ ∧ HoldsRaw p f c ρ C₀ ∧
        g.holds p f (endValues (nξ+B₀+C₀+level) y)

def blockCode {Γ : List Ty} (a : OpenGraph Γ) : UnitCode.Block :=
  (a.width,MatrixCode.formula a.matrix)

/-- Literal typed and raw templates agree for every relevant ground context;
source scopes, witness order and Boolean shape are preserved. -/
def ExactTemplateCodes : Prop :=
  (∀ (Γ : List Ty) (hg : ∀ σ ∈ Γ, σ = .ground) (δ nξ base : Nat)
    (small points : List Nat) (g : OpenGraph (.ground :: Γ)),
    directBlock Γ.length (blockCode g) δ nξ base small points =
      presentedCode (direct hg δ nξ base small points g)) ∧
  ∀ (Γ : List Ty) (hg : ∀ σ ∈ Γ, σ = .ground) (nξ level : Nat)
    (b c : OpenGraph Γ) (g : Presented DirectCtx),
    insertedBlock Γ.length nξ level (blockCode b) (blockCode c) (presentedCode g) =
      presentedCode (inserted hg nξ level b c g)

/-- Exact literal ground Boolean compiler outputs on each fiber, with the
existing counterexample interpretation (these are not a decision oracle). -/
def ExactFiberCompiler : Prop :=
  ∀ (p : Policy) (f : Nat → Nat), FullAddition.Targets.SourceGrowth f →
  ∀ (Γ : List Ty) (hg : ∀ σ ∈ Γ, σ = .ground)
    (a : Presented Γ) (ρ : Variable Γ .ground → Nat),
    let s := closeAt a hg ρ
    let c := s.matrix.toProgram
    let output := compiledFiberCode (presentedCode a) (externalValues ρ)
    (s.holds p f ↔ a.holds p f ρ) ∧
    fiberInputCode (presentedCode a) (externalValues ρ) =
      (s.variables,RawSourceDAG.InputCompiler.encodeInput s.matrix.toInput) ∧
    output = (RawPlanComparisonTargets.encodeComparison (BooleanCompiler.strictPair c),
      RawPlanComparisonTargets.encodeComparison (BooleanCompiler.weakPair c)) ∧
    (Strict p f (BooleanCompiler.strictPair c).1.term (BooleanCompiler.strictPair c).2.term ↔
      ¬ a.holds p f ρ) ∧
    (Weak p f (BooleanCompiler.weakPair c).1.term (BooleanCompiler.weakPair c).2.term ↔
      ¬ a.holds p f ρ)

/-- A unit-open current arbitrary paid certificate implies the full literal
open actual-source graph and original application insertion.
Both raw programs produce these very formulas on the literal source codes. -/
def ExactNumbered : Prop :=
  ∀ (p : Policy) (f : Nat → Nat), Computable f → FullAddition.Targets.SourceGrowth f →
  ∀ (Γ Ξ : List Ty) (σ τ : Ty)
    (B : OriginalTerm Γ (.arrow σ τ)) (C : OriginalTerm Γ σ)
    (K : OriginalTerm Ξ (Ty.curriedGround 1)) (b δ : Nat) (h : Paid p f B C K b δ),
    ∃ (g : Presented DirectCtx) (a : Presented (.ground :: groundCtx Γ)),
      let k : KInput := (Ξ.map SyntaxCode.typeCode,SyntaxCode.encodeTerm K,δ)
      let input : OriginalInput := (Γ.map SyntaxCode.typeCode,SyntaxCode.encodeTerm B,SyntaxCode.encodeTerm C,k)
      directCode p f k = some (presentedCode g) ∧
      insertCode p f input = some (presentedCode a) ∧
      (∀ t y : Nat, g.holds p f (endValues t y) ↔
        actualOrdinalNorm h.paidHead ≤ t ∧ y = J f h.paidHead t) ∧
      (∀ t : Nat, actualOrdinalNorm h.paidHead ≤ t → ∃! y, g.holds p f (endValues t y)) ∧
      ∀ (ρ : Variable Γ .ground → Nat) (y : Nat),
        a.holds p f (resultValues (fun x => ρ (oldGround x)) y) ↔
        CurrentAbsolute.Scalar p f (ExistentialPlan.inputs ρ) (.app B C) y

/-- Separate uniform-in-source computation with fixed actual effective p/f.
No algorithm for deciding unpaid certificate validity is asserted. -/
def EffectiveHeadGraph : Prop :=
  Computable (fun d : UnitCode.Block × List Nat => compiledFiberCode d.1 d.2) ∧
  ∀ (p : Policy), PolicyShape.Effective p → ∀ (f : Nat → Nat),
    Computable f → FullAddition.Targets.SourceGrowth f →
    Computable (directCode p f) ∧ Computable (insertCode p f)

/-- Source theorem plus every actual support, result representation and
finite Boolean/effectivity bridge needed to rule out unverified suppliers. -/
def Full : Prop := Foundation ∧ UnitCodeSupport ∧ ExactS ∧ ExactDirectTemplate ∧
  ExactInsertedTemplate ∧ ExactTemplateCodes ∧ ExactFiberCompiler ∧ ExactNumbered ∧ EffectiveHeadGraph

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.Targets
