# UNIFORM-POLICY-COMPILER: source map (Opus A, round 2)

Targets: `LogicLineages/PermittedControl/UniformPolicyCompilerTargets.lean`, sha256
`5ee4f86932723be0b6ce8bf9a718da2090a0190f5c74760bfb12cd96efddd62e`. It was frozen after compiling alone (receipt
`1795396681854541805-3225971`) and has not been edited since.

This serves `p17/CORRESPONDENCE-REVIEW.md` §1 and §4. The review found that the thm:main comparator compiles each
policy with its own `Computable` proof, so nothing is uniform in a policy program that is supplied as input. The
repair is one partial recursive function that takes the policy program at runtime.

## Statements (frozen)
- `Calibrated compilePolicy`: take any program `e` that realizes a policy `p` in the sense of #1433, `RealizesPolicy`.
  Then for every raw context length `d` and every raw term code `c`, `compilePolicy (e,d,c)` equals
  `Part.some (PolicySourceInterface.compile p d c)`. This includes the rejection `none`.
- `ExactUniformCompiler`: there is a `compilePolicy : Code × Nat × Nat →. Option EncodedVector` with
  `Partrec compilePolicy ∧ Calibrated compilePolicy`. The existential is outside every quantifier over `e` and `p`.

## Gated
- `UniformPolicyCompiler.exactUniformCompiler : ExactUniformCompiler` in module
  `LogicLineages.PermittedControl.UniformPolicyCompilerProof`.
  - Receipt `1795398807501890642-3253060`.
  - `#print axioms` gives `[propext, Classical.choice, Quot.sound]`, for `compilePolicyPartrec`,
    `compilePolicyCalibrated` and `exactUniformCompiler`.

## Uniformity finding
- The policy reaches `PolicySourceInterface.compile` only through `PolicyShape.macroCode p tag n xs`. That
  includes `repeatCode`, which is `macroCode` at arity `count-1`.
- It never reaches it through `Effective p` or through a classically chosen witness.
- So nothing in the existing compiler is non-uniform in the selector program, and no declaration is named as a
  finding.
- The non-uniformity the review found lives only in the per-policy *proofs* of computability, which are of the
  form `Effective p → Computable …`. It is not in the definitions.

## Technique
Technique (a): structural lifting, through Kleene's recursion theorem.
- Technique (b), bounded tabulation of the selector, was rejected. The arities queried depend on the data:
  `scalarRepeat` is queried at `factorCode level h`, computed from earlier output.
- Generic infrastructure is in `UniformPolicyCompilerFixProof`:
  - `decodeEval c a` decodes `c.eval (encode a)`.
  - `exists_fix Φ hΦ` says: if `fun (c,a) => Φ (decodeEval c) a` is `Partrec`, then some `G` satisfies
    `Partrec G ∧ ∀ a, G a = Φ G a`. It is proved from `Nat.Partrec.Code.fixed_point₂`.
  - `pbind` is bind inside `Part (Option _)`, keeping an inner `none` as rejection. `pbind_calibrated` is its
    calibration rule.
  - `pite` is a partial if-then-else on a computable test.
- Each source recursion becomes a one-step functional. Its recursive calls go through `decodeEval` and its macro
  calls go through `macroEval` (#1433, `macroPartrec` / `exactMacroCalibration`).
- Inner folds over `List.range` become `Nat.rec`, which is `Partrec.nat_rec`.
- Calibration is by strong induction on the term code, against the existing equation lemmas. Branches are taken
  by `rw [if_pos/if_neg/dif_pos/dif_neg]`, in the same `dite` order as the source.

## Modules (dependency order)
| Module | Content | Receipt |
|---|---|---|
| `UniformPolicyCompilerTargets` | frozen `Calibrated`, `ExactUniformCompiler` | `1795396681854541805-3225971` |
| `UniformPolicyCompilerFixProof` | `decodeEval`, `exists_fix`, `pbind`, `pite` | `1795397134099696045-3230876` |
| `UniformPolicyCompilerPartialTargets` | frozen layer 1: `ExactUniformPartial` | `1795397337237643504-3231929` |
| `UniformPolicyCompilerPartialProof` | `exactUniformPartial`: `PolicyPartial.run` (coordinate merge, tags 3/4/5/6) as a fixed point | `1795397543874623162-3233154` |
| `UniformPolicyCompilerPiecesProof` | `repeatP`, `recursorP`, `boxTailP`, `applicationP`, `partialsP`, `coordinateP`, `resultP`, `abstractionP`, each with a `…Partrec` and a `…Cal` matching `PolicyShape.repeatCode`, `PolicyConstructors.*` and `PolicyAbstraction.*` | `1795397903459563104-3235640` |
| `UniformPolicyCompilerStepProof` | `primeP` and `primeCal`; the assignment step `assignStep` split into `contBranch` / `appBranch` / `appMid` / `appInner` / `lamBranch` / `lamInner`; `assignStepPartrec` | `1795398797920438628-3252959` |
| `UniformPolicyCompilerProof` | `assignU` (fixed point of `assignStep`); `assignUCal` against `PolicyAssignment.assignmentCode`; `compilePolicy`; `exactUniformCompiler` | `1795398807501890642-3253060` |

## Correspondence
The final program is:
```
compilePolicy (e,d,c) := pbind (assignU (e, replicate d 0, c)) (fun v => Part.some (compileVectorCode v))
```
It is the literal transcription of
`PolicySourceInterface.compile p d c := assignmentCode p (replicate d 0) c >>= compileVectorCode`, with:
- `macroCode p` replaced by `macroEval e`;
- the two well-founded recursions (`PolicyPartial.run`, `assignmentCode`) replaced by Kleene fixed points.

`compileVectorCode` is policy-free and is used through `ordinalSyntaxVectorCompilerPrimitiveRecursive`.

## Scope notes
- Nothing is claimed about programs that realize no policy. There `compilePolicy` may diverge or return anything.
- Calibration is exact equality of `Part` values. On realizing programs, the program halts on every input.
