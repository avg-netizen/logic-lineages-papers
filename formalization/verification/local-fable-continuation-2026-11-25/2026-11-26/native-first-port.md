Not compiled. The first native target is file 1 of the manifest, `NumberedWindowAddressApplicationTargets`. It needs no other new file: all four of its imports already exist.

Destination: `LogicLineages/NativeModule/PersistentMarking/NumberedWindowAddressApplicationTargets.lean`
Lean target: `LogicLineages.NativeModule.PersistentMarking.NumberedWindowAddressApplicationTargets`

```lean
module

public import LogicLineages.PersistentMarking.NumberedWindowAddressApplication
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticScalarTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalApplication
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPathWitnessTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowAddressApplicationTargets
open NumberedWindowSyntax NumberedWindowSimulationData NumberedWindowExternalApplication
open NumberedWindowAddressApplication NumberedWindowArithmeticScalarTargets
open NumberedWindowArithmeticClassAddress NumberedWindowArithmeticAllContextBits
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticLeastClass NumberedWindowPathWitnessTargets

def decodedApplication (S : Spine.Signature) (K : List Ty) (source argument : Nat) : Option Nat := do
  let q ← decodeAddress source
  let u ← decodeAddress argument
  let .arrow domain result := q.result | none
  if canonicalBit S K q && canonicalBit S K u &&
      decide (q.context = u.context) && decide (domain = u.result) then
    let Q ← decodeTerm q.least
    let U ← decodeTerm u.least
    (leastCode S K q.context result (.auxApp domain result Q U)).map
      (fun k => encodeAddress ⟨q.context,result,k⟩)
  else none

def ExactDecodedApplication : Prop :=
  ∀ S K source argument,
    application (fixed S K) source argument = decodedApplication S K source argument

def ExactClassApplication : Prop :=
  ∀ S K Γ σ τ (hk : DecisionSourceUniverse.Closed K)
    (q : Class S K (finiteC Γ) (.arrow σ τ)) (u : Class S K (finiteC Γ) σ) i j,
    ActualCodeAt S K Γ (.arrow σ τ) i q → ActualCodeAt S K Γ σ j u →
      ∀ value, decodedApplication S K (encodeAddress ⟨Γ,.arrow σ τ,i⟩)
        (encodeAddress ⟨Γ,σ,j⟩) = some value ↔
        ∃ k, value = encodeAddress ⟨Γ,τ,k⟩ ∧
          ActualCodeAt S K Γ τ k (appClass hk q u)

end LogicLineages.PersistentMarking.NumberedWindowAddressApplicationTargets
```

The body from the `namespace` line onward is the legacy file verbatim (`LogicLineages/PersistentMarking/NumberedWindowAddressApplicationTargets.lean:6-37`). Only the header differs.

## Where each symbol comes from

Every defining file below has `module` and `@[expose] public section`, and every link in each chain is a `public import` line I read. In the table, N/ is `LogicLineages/NativeModule/PersistentMarking/`.

| Symbol | Defined at | Reached from this file by |
|---|---|---|
| `application` | shared `NumberedWindowAddressApplication.lean:22` | direct import |
| `fixed` | N/`NumberedWindowArithmeticScalarTargets.lean:16` | direct import |
| `appClass` | N/`NumberedWindowExternalApplication.lean:24` | direct import |
| `ActualCodeAt` | N/`NumberedWindowPathWitnessTargets.lean:15` | direct import |
| `ClassAddress`, `encodeAddress`, `decodeAddress` | N/`NumberedWindowArithmeticClassAddress.lean:15,20,30` | `ScalarTargets:8` → `AllContextBits:3` |
| `canonicalBit` | N/`NumberedWindowArithmeticAllContextBits.lean:15` | `ScalarTargets:8` |
| `leastCode`, `finiteC` | N/`NumberedWindowArithmeticLeastClass.lean:18,12` | `PathWitnessTargets:3` → `ClassPathWitnessBits:4` |
| `Class`, `WindowCarrier`, `classOf` | N/`NumberedWindowSimulationData.lean:46,41,49` | `ExternalApplication:4` |
| `decodeTerm` | N/`NumberedWindowArithmeticTermCode.lean:79` | see below |
| `NTerm.auxApp` | N/`NumberedWindowSyntax.lean:21` | `ArithmeticTermCode:3`; see below |

Two entries rest on usage evidence, because I did not read every link:

- **`decodeTerm`** is used unqualified at `AllContextBits:16`, and that file's only imports are two `public import` lines. So it is in the public closure of `AllContextBits`, which this file reaches through `ScalarTargets:8`.
- **`NTerm.auxApp`** is used at `ExternalApplication:14`, whose only imports are also public.

The same argument covers three more things the body needs:

- `DecisionSourceUniverse.Closed` appears at `ExternalApplication:11`.
- `Spine.Signature` and `Ty` appear at `ArithmeticLeastClass:18`.
- The decidable equalities behind `decide (q.context = u.context)` and `decide (domain = u.result)` are used the same way at `AllContextBits:33`.

This file contains only definitions, so it needs names and types visible. It does not unfold any imported body; that requirement starts with file 2.

## Boundary with the shared `NumberedWindowAddressApplication`

Nothing is moved or duplicated there.

- **Different namespaces.** The shared file declares `arrowView`, `applyAddresses`, `application` and `graph` in `…NumberedWindowAddressApplication`. This file declares `decodedApplication`, `ExactDecodedApplication` and `ExactClassApplication` in `…NumberedWindowAddressApplicationTargets`. The full names are disjoint; the `open` line only brings names into scope.
- **The shared file is free of the `fixed` clash.** Its single import is `LogicLineages.PersistentMarking.NumberedWindowScalarAlgorithm`, which the native `ScalarTargets` also imports at its line 3. It is generic in `Settings` and never mentions `fixed`.
- **The real duplicate is the legacy `NumberedWindowAddressApplicationTargets`.** It declares the same three names in the same namespace. The native file and the legacy file must never be in one import closure. The legacy file stays as it is for its current importers.

## What this target tests

A successful check confirms, at the cost of three definitions:

- a native-prefix file can import a shared `PersistentMarking` module file alongside native ones;
- the native `fixed`, `appClass` and `ActualCodeAt` have the types the legacy statements expect;
- the ten opened namespaces all exist in the native closure.

Files 2–4 are the next step, with top target `…NumberedWindowAddressApplicationChecks`.
