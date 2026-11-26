# Paper 16: modular literal type-guard reselection at actual Settings

Scope: source-only candidate. Exact native and axiom gates pending. This
is a new modular packet, not a repair or a weakening of the failed
fixed-settings aliases. Their sources and diagnostics are untouched.

- The definitions use the original `Settings`. The physical guard is
  literally `conjunction T (grammarTypeAt s)`, where `grammarTypeAt s`
  runs actual scratch membership on `[encode s.types,ty]`.
- `exact_SettingsRefitGuardCalibration` retains the exact
  `TypeGuardCalibrated s` equality for all naturals, with one explicit
  same-settings list premise `∀ n, n ∈ s.window.1 → n ∈ s.types` and
  original calibration of T. No structural, graph, closure, or decision
  guard is imported into that premise: numerical acceptance of T implies
  actual membership in the window list by the definition of `typeGuard`.
- `exact_OpenSettingsRefitGuardReports` needs neither the list premise
  nor calibration. Both directions use actual object graph rules and the
  same T, grammar list numeral, term, body, and context. Literal numeral
  introduction is obtained from the actual zero/successor graph rules,
  not numerical reflection. This says nothing about the old T alone.
- Targets/proofs are split so the open root does not import the numeric
  target or code. No legacy fixed-settings module is in either closure.
  A future verified fixed inclusion can instantiate the conditional
  numeric theorem, separately; no claimed fixed alias or reinstall here.

| Module suffix | SHA-256 |
| --- | --- |
| `NumberedWindowInternalSettingsGrammarGuardDefinitions` | `cddccc9ab1bb6e9e9a500c4f07ce9fd5278f3bba1ae55555c12787509a9b67b6` |
| `NumberedWindowInternalSettingsGrammarGuardNumericProof` | `03ff308debee0454706b39fe371ef5fb4baeca109824bd4b9945dba15317fde5` |
| `NumberedWindowInternalSettingsGrammarGuardNumericTargets` | `bd6b328959c156de941e29263815c413d1d52f9fdd8aa588717114f2d566b731` |
| `NumberedWindowInternalSettingsGrammarGuardOpenProof` | `7895593935f4daff26497fdbd6f1be317d85a946b5c19746bebea9c2ad958726` |
| `NumberedWindowInternalSettingsGrammarGuardOpenTargets` | `7c65a12f30c9c61ac69424ce2341898c5bdb75649394e350fdf90f6f3e00c828` |
