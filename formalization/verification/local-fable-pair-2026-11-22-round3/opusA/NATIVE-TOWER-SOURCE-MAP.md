# NATIVE-TOWER: source map (Opus A, round 3)

This serves `ordinals.tex` 531–550, the finite-type extractors (B) and (B_T). It closes the gap that
`P16-LEM-REALIZATION-CORRESPONDENCE.md` names: "(D), (R) and `thm:height` need `B_l` for every `l`".

All modules are new, untracked `module` files under `LogicLineages/NativeModule/PersistentMarking/`. They import twins
and module-system originals only. No tracked file and no twin was edited, and no twin was generated.

## Gated

| Module | Content | sha256 | Receipt |
|---|---|---|---|
| `NativeTowerTargets` | frozen definitions plus `NativeTowerRealization` | `a4f51a006a7a2f4f4d93e01905f3d1e8f4c213802560376030a66ba8d0692aec` | `1795402383492741785-3277208` (compiled alone) |
| `NativeTowerSyntaxProof` | typing of every partial tower; substitution acts slot by slot | `a9a69146c43f940c02d50ce15465bad788f09d924541a4ccd0a769dbdf2dc3b5` | `1795402486217973933-3277777` |
| `NativeTowerProof` | `exact_NativeTowerRealization : NativeTowerRealization` | `f3d571c5a76cd69b220f8560b680c3dfc75a2f7306f09b2f7e7d65c7cecc7982` | `1795402619861101760-3278384` (663 modules, all rc 0) |
| `NativeTowerPrintedTargets` | frozen `PrintedTowerRealization` | `a7d91a501cb70e13b405e1333687717e850d06e04f56aa53dfbd59898210c2df` | `1795402698832557428-3278827` (compiled alone) |
| `NativeTowerPrintedProof` | `exact_PrintedTowerRealization : PrintedTowerRealization` | `e34d68237af0dad8f44aff33b94bdb74a6df33cd7c1f61b88a4c3dff438c1c4c` | `1795402711003426157-3278878` (686 modules, all rc 0) |

- Axioms for both theorems: `[propext, Classical.choice, Quot.sound]`.
- Peak RSS is 945,812 KiB, reached at `NativeTowerProof`. The cap is 1,572,864 KiB.

## Statements
- **`NativeTowerRealization`.** Fix a signature `S`, and take any closed native `F : |A_2|` that realizes a semantic
  `φ : A_2`. Then for every `l` there is a closed native term `t` with:
  - `t.val = towerTerm F l`, and
  - `t ⊨_{A_{l+2}} towerValue φ l`.

  The well-foundedness proof is the closed native confined relation's (`exact_ClosedNativeStrictWellFounded`).
- **`PrintedTowerRealization`.** The same statement with `F` the printed `fix` (`ordinalFix = λf:σ→σ. λz:σ. It_ι w f (s z)`)
  and `φ` any semantic `fix` satisfying `OrdinalArithmeticEquations ∧ OmegaArithmeticEquations`, that is,
  `fix f z = orbit ι f (s z) w`, which is `f^ω(z+1)`.
  - The proof is `exact_NativeTowerRealization` at `F := (literalArithmetic S).fix`, whose realization is the 8th
    conjunct of `exact_LiteralNativeArithmeticRealizes`. That theorem is Opus B's twin, in the closure of #1456.
  - The equations have solutions by the gated generic orbit records (`ExactOrdinalArithmeticOrbits`,
    `ExactOrdinalOmegaOrbits`).

## Printed text against the definitions

| Printed (ordinals.tex) | Lean (`NativeTowerTargets`) | Verdict |
|---|---|---|
| "Put A_0=ι and A_{l+1}=A_l→A_l" | `tier 0 = .base`, `tier (l+1) = .arrow (tier l) (tier l)`; `tierType l = |A_l|` | exact |
| `B_l h h_l⋯h_1 = Fix(λα. h^α h_l⋯h_1 0)`, `B_l : A_{l+2}` | `towerValue φ l := curryEnv (l+1) (fun xs => φ (fun α => spineValue l xs α)) _`, typed `Value (tier (l+2))`. The binders `h, h_l, …, h_1` fill environment slots `l+1, l, …, 1`. `spineValue l xs α` is `h^α h_l ⋯ h_1 0`, with `h^α x := orbit A_l h x α` (convention (I), full prefix, all set functions) and `0 = zeroValue`. | exact, with `Fix := φ`. Checks: `towerValue_zero` shows `B_0 h = φ(λα. orbit ι h 0 α)`, and `towerValue_one` shows `B_1 h h₁ = φ(λα. orbit A_1 h h₁ α 0)`. |
| "use fix for Fix" | `φ` is the value realized by the supplied fix term. In the printed instance it is `fix f z = f^ω(z+1)` (line 527, "realize … f^ω(ζ+1)"). | exact. The paper's `Fix` *is* this semantic `fix`. Whether it coincides with Simmons's `Fix` on his helpful functions is part of the calibration, and is not stated here. |
| "For l=0, the inner body is It_ι α h Z" | `spine 0 α a = applied ι α (a 1) Z` | literal; see `towerTerm_zero` |
| "For l≥1, it is (It_{A_l} α h h_l)h_{l-1}⋯h_1 Z" | `spine (m+1) α a = natDown m (applied A_{m+1} α (a (m+2)) (a (m+1))) a`. `natDown` applies slots `m, …, 1` and then `Z`. | literal; see `towerTerm_one` |
| "Prefix the corresponding typed lambdas" | `towerTerm F l = binders (l+1) (fixBody F l boundSlots)` = `λh:|A_{l+1}|. λh_l:|A_l| ⋯ λh_1:|A_1|. F (λα:σ. spine)`. The de Bruijn indices are `α=0`, `h_j=j`, `h=l+1`. | literal |
| "The terminal Z is present in every case" | `towerZero = λz:o.z`, the final argument of every spine | literal. It is the same expression as `NativeOrdinalBasisTargets.ordinalZero`. |
| "The iterator theorem and the lambda fundamental lemma verify the realization of (B)" | The proof uses `exact_NativeIteratorRealizesFullPrefix` (with uniqueness from `exact_FullPrefixOrbitExists`), the abstraction rule `exact_NativeLambdaRealization` applied `l+2` times to closed substitution instances (bodies named by `exact_ClosedNativeBeta`), and application (the definition of arrow realization). | as printed, under the abstraction-rule reading. No general fundamental lemma is needed or used. |
| "All names here abbreviate finite expressions in the original native constants, lambdas and applications" | `towerClosed`: `ClosedNative S (towerTerm F l) |A_{l+2}|` for every `l` | checked |

## Proof route
- **Syntax module.** Partial towers carry a slot function `a`. Slots `≤ k` hold bound variables and slots `> k` hold
  closed terms.
  - `partialClosed` types every partial tower. It re-derives the `NativeIn` helpers from the legacy private ones, and
    uses `ClosingProof.weakening` and `exact_ClosedNativeIterator`.
  - `substBinders`, `substFixBody` and `substSpine` push substitution through the term structurally.
  - `nearer`, `atSlot` and `unchanged` are the slotwise facts. They rest on `ClosedSyntaxProof.term` and `closedShift`.
  - This is the "syntactic de Bruijn bookkeeping" called for in round 2, gated as its own module.
- **Realization.** `partialRealizes` is downward induction on the number `k` of remaining binders.
  - Step `k+1 → k`: apply the abstraction rule. The substituted body is the partial tower at `k` with slot `k+1` closed.
  - Base `k=0`: `F ⊨ φ`, applied to `λα.Sp`. `λα.Sp` is realized by the abstraction rule plus `spineRealizes`, which is
    the iterator followed by application along the slots and `Z ⊨ 0`.

## Coverage of (D), (R), `thm:height`
- **Covered.**
  - The realization of every `B_l` (every `l`) by the printed native term, at the printed `fix`, unconditionally.
  - With any fix realizer, generically.
- **Remaining for (R) "r_σ(t_n) ≥ ψ_B(a_n)", split three ways.**
  1. *Syntactic/definitional.*
     - What is needed: `t_n` (the native (D) with `N_B = B_1 B_0 Next`, `Δ_0 = N_B(ω)`, `Δ_1 = N_B Γ_0`,
       `Δ_{l+2} = B_l ⋯ B_0 N_B Γ_0`) realizes the *semantic* composite `Δ_n' := B_l(⋯)(N_B)(Γ_0')`.
     - The materials are mine, plus Opus B's `literalNext ⊨ fix pow` and `w ⊨ ω`.
     - Realizing an application is the definition of arrow realization, so this is an n-uniform application spine: one
       more small induction, not formalized.
     - Note that `Γ_0` itself is printed as `N_B(ω)`, so it too is a semantic composite.
  2. *External literature.* The identification `Δ_n' = ψ_B(a_n)` comes from Simmons 2004/2008 (helpfulness,
     Thm 5.10; Thm 6.1 / Cor 6.2; the identity after Lemma 6.6), together with the tameness check. `ψ_B` and the
     coefficient norm are not defined in the repository.
  3. Then `r_σ(t_n) ≥ Δ_n'` follows from realization at ι by definition. Combined with 2, that gives (R).
- **`thm:height`** needs (R), `lem:tower-cofinality` (external: (P), ψ_B, and the BH identification via Pohlers) and
  `thm:upper`.
- **Nothing here depends on Simmons, ψ_B or BH.**
