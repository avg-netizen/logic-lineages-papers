# Uniform policy compiler — interface (Opus A, round 2)

Frozen: `LogicLineages/PermittedControl/UniformPolicyCompilerTargets.lean`
(sha256 `5ee4f86932723be0b6ce8bf9a718da2090a0190f5c74760bfb12cd96efddd62e`, receipt `1795396681854541805-3225971`).
Namespace `LogicLineages.PermittedControl.UniformPolicyCompiler`.

```lean
open OrdinalComparison.Source.ForwardTranslation (EncodedVector)   -- = Nat × List Nat
open PermittedControl.PolicySuppliedCodeMacro (RealizesPolicy)

def Calibrated (compilePolicy : Nat.Partrec.Code × Nat × Nat →. Option EncodedVector) : Prop :=
  ∀ (e : Nat.Partrec.Code) (p : Policy), RealizesPolicy e p →
    ∀ d c : Nat, compilePolicy (e,d,c) = Part.some (StandardControlCurrent.PolicySourceInterface.compile p d c)

def ExactUniformCompiler : Prop :=
  ∃ compilePolicy : Nat.Partrec.Code × Nat × Nat →. Option EncodedVector,
    Partrec compilePolicy ∧ Calibrated compilePolicy
```

Arguments: `(policy program e, context length d, term code c)`. On every program realizing a policy, it is
total on every raw `d`, `c` and equal to `PolicySourceInterface.compile p d c`, including the rejection `none`.

Use it as `obtain ⟨compilePolicy, hpart, hcal⟩ := (h : ExactUniformCompiler)`. Until it is gated, take
`ExactUniformCompiler` as a hypothesis. The theorem will be `UniformPolicyCompiler.exactUniformCompiler`.

**GATED 2026-11-22:** `UniformPolicyCompiler.exactUniformCompiler : ExactUniformCompiler`.
- Module `LogicLineages.PermittedControl.UniformPolicyCompilerProof`, receipt `1795398807501890642-3253060`.
- Axioms are standard.
- Import that module and discharge the hypothesis with `exactUniformCompiler`.
