# Paper 16: conditional fresh (A) installation with chosen direct core

Source freeze only, pending native gates. Paper 16 `sections/ordinals.tex:74–98`
(SHA-256 `526aa249902b4e4bf00f45bee770bdcdc9f9b39c2dc341778834600b7f8bf1b5`)
describes the original positive relation, finite direct multiset replacement,
and the pair of typed accessibility equations (A) in one operator. This packet
selects that same tagged presentation with one **new** physical direct checker.
It does not prove universal `I` or `J` membership, multiset union or (T), and
does not use an old accessibility derivation in the new body.

* `ExactReinstall` takes the exact three numeral calibrations from the first
  three fields of the old `Evaluates (checks xs s) i j r dOld` (no old direct
  proof/tree/meaning required) and an explicit `CountFit count`. It installs
  precisely `dCore i r count`. Its fourth fresh `Evaluates` conjunct uses
  `exact_NumericDCore`, with the same `i`, the same original `r` and the original
  semantic `NumberedWindowConcreteCheckers.direct` / `NumberedWindowAddressCheckers.direct`.
* It proves fresh `Interprets` using original exact calibration, and builds
  fresh `Rules` using actual original equation, carrier extraction, successor,
  certified successor, and introduction theorems. Each conclusion uses the
  same `p := data i j r (dCore i r count)`; no application rule from #660, no
  inferred old/new body equality, and no transport of membership.
* `ExactSelectedReinstall` separately obtains actual `i,j,r` from #571
  `NumberedWindowInternalAccessibilityChecks.exact_ConcreteInternalAccessibility`,
  projects only its numeric first three, and uses `ExactReinstall`. This leaf
  transits `Mathlib.Tactic.Linarith` by the old concrete choice (#571 →
  `NumberedWindowConcreteFormulaChecks`); the held-three reinstall leaf does
  not. Gate the two independently; no alternate provider/cache or pin change.
* `CountFit` is assumed, not instantiated by any observer in this packet.
  Numeral calibration is not open count reflection. Nothing here produces an
  arbitrary-open direct multiset matching theorem or closes the printed
  arithmetic-accessibility lemma.

| New leaf `NumberedWindowInternalDirectCoreReinstall…` | SHA-256 | Local closure |
| --- | --- | --- |
| `Targets` | `73aeee78aa422c7d32ec8fe0366e094b3f61228281820d1987ae9e96ba9b20a5` | 1115 |
| `Proof` | `7d0a94d66df2fe5673903f88b6b026e40d1335655b856e07ba22949f392d8011` | 1210 |
| `SelectedProof` | `b7047a490c3669f14da90cf0f70b669927a0f69bd22718a7d0e89acf2369b8d7` | 1298 |

Supplier SHA-256 pins (unchanged):

| PersistentMarking leaf | SHA-256 |
| --- | --- |
| `NumberedWindowInternalDirectCoreNumericProof` | `c61e5ff51c761d2f4abd25e3c57987622d96224af28205c0e903351e17bfbd40` |
| `NumberedWindowFormulaCalibrationChecks` | `2d80636169f08bc8a5b4d1a3daec50e7065157fa0b0588c23a7f29e128392316` |
| `NumberedWindowInternalAccessibilityTargets` | `44378685ac2fc95e2ff475c1f7da3ad693f0cf7b8268bf73559193369adb4299` |
| `NumberedWindowInternalAccessibilityChecks` | `6a1071a691aca785abd711f15238314d7328ae980bc352e6a298226a430c309d` |

Exact gates `NumberedWindowInternalDirectCoreReinstallProof.exact_Reinstall`
then `NumberedWindowInternalDirectCoreReinstallSelectedProof.exact_SelectedReinstall`.
