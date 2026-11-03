module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedGuardDescentDefinitions
public import Mathlib.Computability.Primrec.List
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedGuardDescent.Targets
open BalancedSyntax BalancedEvaluation

/-- One fixed actual lower certificate and ONE raw valuation throughout.
Only genuine labels and positivity on their actual support are needed for
semantics. Support has its own explicit premise and needs no positivity. -/
def ExactGuardTranslation : Prop :=
  (∀ (Γ : List Nat) (C : Certificate Γ) (lower : Lower Γ)
    (labels : List (Syntax Γ)) (ν : Nat → Nat),
    LowerCorrect Γ C lower ν →
    (∀ T ∈ labels, genuineExpression Γ T) →
    (∀ i ∈ labelSupport Γ C labels, 0 < ν i) →
    ∀ p : CommonHeadLargeGuards.Formula,
      (translateGuard Γ lower labels p).eval ν ↔ p.eval (labelValuation Γ C labels ν)) ∧
  (∀ (Γ : List Nat) (C : Certificate Γ) (lower : Lower Γ)
    (labels : List (Syntax Γ)), LowerSupport Γ C lower →
    ∀ (p : CommonHeadLargeGuards.Formula) (i : Nat),
      i ∈ (translateGuard Γ lower labels p).variables → i ∈ labelSupport Γ C labels)

/-- The accepted ordered completeInput/lowerPart labels supply genuine
lower terms and original support under C.1. The semantic premise is NOT
discharged here: the final recursive compiler must prove it by induction.
No independently valued basis or positivity outside original support occurs. -/
def ActualSourceDescent : Prop :=
  (∀ (k : Nat) (Γ : List Nat) (C : Certificate (k :: Γ))
    (E F : Upper k) (desired : Int) (lower : Lower Γ) (ν : Nat → Nat),
    genuineCertificate (k :: Γ) C →
    genuineExpression (k :: Γ) E → genuineExpression (k :: Γ) F →
    (∀ i ∈ BalancedLargeGuards.sourceAmbient k Γ C E F, 0 < ν i) →
    LowerCorrect Γ C.1 lower ν →
    ((sourceTranslation k Γ C E F desired lower).eval ν ↔
      (BalancedLargeGuards.sourceFormula E F desired).eval
        (BalancedLargeGuards.sourceValuation k Γ C E F ν)) ∧
    ((sourceTranslation k Γ C E F desired lower).eval ν ↔
      (∀ a ∈ (comparisonRow E F).atoms,
        BalancedRow.threshold (comparisonRow E F) ≤
          BalancedRow.input (basisValues k Γ C ν) a.2) ∧
      Int.sign ((value (k :: Γ) C E ν : Int) - (value (k :: Γ) C F ν : Int)) = desired)) ∧
  (∀ (k : Nat) (Γ : List Nat) (C : Certificate (k :: Γ))
    (E F : Upper k) (desired : Int) (lower : Lower Γ),
    LowerSupport Γ C.1 lower → ∀ i ∈ (sourceTranslation k Γ C E F desired lower).variables,
      i ∈ BalancedLargeGuards.sourceAmbient k Γ C E F)

/-- Exact balanced source-code children, including out-of-range defaults,
arbitrary numeral bounds and ignored Boolean children. Assembly is literal
existing postfix encoding, not just equality of truth values or runtime output. -/
def ExactPostfixSubstitution : Prop :=
  (∀ (Γ : List Nat) (C : Certificate Γ) (labels : List (Syntax Γ)) (q : CommonHeadCompiler.Instruction),
    child Γ (encodeCertificate Γ C) (labels.map (encodeSyntax Γ)) q =
      encodeCall Γ C (typedChild Γ labels q)) ∧
  (∀ (Γ : List Nat) (lower : Lower Γ) (labels : List (Syntax Γ)) (code : Code),
    (typedResults Γ lower labels code).length = code.length) ∧
  (∀ (Γ : List Nat) (lower : Lower Γ) (labels : List (Syntax Γ))
    (p : CommonHeadLargeGuards.Formula),
    assemble (CommonHeadCompiler.encode p)
        (typedResults Γ lower labels (CommonHeadCompiler.encode p)) =
      (translateGuard Γ lower labels p).encode)

/-- Every ORIGINAL guard instruction has exactly one child. All child shapes
strictly drop the outer level, even on arbitrary raw inputs and for ignored
Boolean children. Actual-source calibration pays the existing adapter laws,
retains C.1, and uses the same typed comparator results in the same order. -/
def ExactActualCallsAndDescent : Prop :=
  (∀ (k : Nat) (Γ : List Nat) (C E F : Nat) (desired : Int),
    (sourceChildren k Γ C E F desired).length =
      (BalancedSourceAdapter.formulaCode k E F desired).length ∧
    ∀ a ∈ sourceChildren k Γ C E F desired, measure a < (k :: Γ).length) ∧
  (∀ (k : Nat) (Γ : List Nat) (C : Certificate (k :: Γ))
    (E F : Upper k) (desired : Int) (lower : Lower Γ),
    let c := encodeCertificate (k :: Γ) C
    let e := encodeSyntax (k :: Γ) E
    let f := encodeSyntax (k :: Γ) F
    let labels := BalancedLargeGuards.sourceTerms k Γ C E F
    let code := CommonHeadCompiler.encode (BalancedLargeGuards.sourceFormula E F desired)
    sourceChildren k Γ c e f desired =
      code.map (fun q => encodeCall Γ C.1 (typedChild Γ labels q)) ∧
    sourceAssemble k e f desired (typedResults Γ lower labels code) =
      (sourceTranslation k Γ C E F desired lower).encode)

/-- Unconditional uniform primitive recursion of the actual numeric maps on
ALL raw shapes, certificates, labels, commands, source codes and result lists.
No semantic lower comparator or source-validity premise supplies effectivity.
This is a single-level call/assembly interface, not a recursive compiler. -/
def UniformPrimitiveRecursive : Prop :=
  Primrec (fun p : List Nat × List Nat × Nat => labelCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : List Nat × Nat × List Nat × CommonHeadCompiler.Instruction =>
    child p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  Primrec (fun p : List Nat × Nat × List Nat × Code =>
    children p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  Primrec₂ instructionCode ∧
  Primrec₂ assemble ∧
  Primrec (fun p : Nat × List Nat × Nat × Nat × Nat × Int =>
    sourceChildren p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) ∧
  Primrec (fun p : Nat × Nat × Nat × Int × List Code =>
    sourceAssemble p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) ∧
  Primrec measure

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedGuardDescent.Targets
