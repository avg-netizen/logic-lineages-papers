# Model theory and algebra formalization

## User pause handoff — 29 October 2026

**Local lane paused for the external-agent takeover. No compiler or author
is live in this lane. No automatic resume and no Git operation occurred.**
The last native attempts were prelaunch memory deferrals, not running jobs.
This handoff supersedes historical running/HOLD descriptions below.

**Accepted:** nine exact component gates, with expanded types, source and
semantic SHA256s, declarations and axiom closures in
`LogicLineages/ModelsAlgebra/ACCEPTED-COMPONENTS.json`.

- Forest no-common-upper, maximal extension and attained width/leaf-count
  bound: receipt `1793249096318899425-2.json`.
- Actual p-step image, finite filtration image and saturated-intersection
  image: `1793249492913314109-2.json`.
- Actual ordinal antitonicity, image below a kernel cut and literal quotient
  filtration equality: `1793251592919663407-2.json`.

The complete **first displayed conclusion** of paper 01's
`lem:quotient-filtration` is checked, generalized to arbitrary cuts.
The full numbered lemma remains pending until its actual Ulm-map
isomorphism/rank conclusion passes. No full numbered target in this lane
is marked complete. Only the permitted standard foundations occur.

**Next existing source target:** the remainder of that same lemma.
`PGroups/UlmDefinitions.lean` constructs actual p-socles, quotient layers
and their ZMod action from p-annihilation. `UlmMapDefinitions.lean` constructs
the actual induced map. `UlmTargets.lean` freezes bijectivity under the local
kernel bound; `UlmIsomorphism.lean` and `UlmStatementChecks.lean` contain its
candidate and exact gate. `QuotientUlmDefinitions.lean`,
`FullQuotientTargets.lean`, `OmegaCutFacts.lean`,
`FullQuotientFiltration.lean` and `FullQuotientStatementChecks.lean` contain
the literal omega-cut map, full two-conclusion comparison, candidate and gate.
**All these new Ulm/full-lemma files are uncompiled.** Their specifications
were hashed before their corresponding bijectivity/full proof candidates.
The last attempts stopped before launch at 894/866 MiB available memory:
receipts `1793252382168239810-2.json` and `1793253122086677454-2.json`.
No Ulm source diagnostic exists yet. First obtain those diagnostics and repair
them while preserving the frozen mathematical types; do not infer success
from the written candidate. Once independently resumed, the next command is:

```sh
python3 scripts/check.py LogicLineages.ModelsAlgebra.PGroups.UlmStatementChecks LogicLineages.ModelsAlgebra.PGroups.FullQuotientStatementChecks
```

The older transfinite `open Order` and explicit `Set.Iio` family fixes
already passed; they do not need repair again. `PGroups/PROOF-PLAN.md`
records the dependency chain. Full Scott syntax/semantics, Ulm/Zippin and
back-and-forth suppliers remain unfinished; forest graph representation,
Carter's full decision proof, binary-tree JEP classification and age
construction also remain unfinished.

**Differential family:** fixed `Differential/Targets.lean` passed, but no
differential proof gate is accepted. Original and minpoly-degree constants,
rational-linearity bridge, spectral independence, jet semantics, generated
fields and finite-extension candidates are preserved. The pure Separable
import probe itself timed out without a theorem body
(`1793247750664080886-2.json`); the separate minpoly-degree path also timed
out (`1793248193560190399-2.json`). Root subsequently measured actual worker
page-I/O waits, not a mathematical counterexample. No unchanged import retry
is authorized by this pause. The two full constraint criteria and their
effective algorithms remain pending. See `Differential/PROOF-PLAN.md`.

**Environment and outside material:** use the shared runner, pinned Lean
`v4.32.0-rc1` and Mathlib commit `360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`.
Current native guards are managed heap 1536 MiB, actual RSS 1024 MiB,
CPU 90 s, wall 180 s, prelaunch available memory 1024 MiB, system floor
256 MiB. No private source import or 3.1.3 module was selected. The
development Mathlib cache is inside this repo's calculator checkout;
the installed toolchain lives under `/home/other/.elan/toolchains/`.
Optional primary-text copies outside this papers repo, verified by title
and version during the handoff, are:

- `projects/inverse/logic-lineages/collected-papers/text/2024-scott-complexity-of-reduced-abelian-p-groups.txt`
  (ACM, arXiv:2407.06940v1).
- `projects/inverse/logic-lineages/collected-papers/text/2024-on-the-joint-embedding-property-for-cographs-and-trees.txt`
  (Carter, arXiv:2409.06127v1).
- `projects/inverse/logic-lineages/collected-papers/text/2026-scott-analysis-below-the-vaught-ordinal.txt`
  (GRT, arXiv:2606.15205v2).

They are bibliographic aids, not Lean dependencies. Each paper's public
`SOURCES.md` pins the remaining references. No wider-vault convention is
needed to understand the current actual source targets.

Scope: papers 01 (Scott complexity of countable abelian p-groups),
03 (finite order-forest joint embedding), and 15 (differential-field
constraint decisions). This lane owns `LogicLineages/ModelsAlgebra/`.
The exact full paper targets remain obligations until their actual
unconditional signatures and axiom reports pass the shared verifier.

## Current work

Three actual forest components passed the frozen statement and kernel-axiom
gates in `build-reports/1793249096318899425-2.json`:

- Incomparable forest vertices have no common upper bound (axiom closure
  empty).
- Every vertex of a finite partial order lies below a maximal vertex
  (only the standard three foundations).
- For every finite forest and every bound m, all antichains have at most
  m vertices exactly when the set of maximal vertices has at most m
  vertices (only the standard three foundations). The candidate proves
  that the maximal-vertex set is itself an antichain, so the bound is
  attained.

The exact declarations, expanded types, specification/candidate/semantic
source hashes and correspondence to paper 03's width paragraph are in
`ModelsAlgebra/ACCEPTED-COMPONENTS.json`. These facts do not complete the
numbered JEP-width theorem, Carter's decision theorem or the full graph
bridge.

Three actual p-filtration components also passed exact statement and
transitive axiom gates in `build-reports/1793249492913314109-2.json`:
multiplication-by-p images commute with homomorphisms; every finite
stage commutes with a surjective image; and arbitrary subgroup
intersections commute with a surjection when every subgroup contains
its kernel. Only the standard three foundations occur (the first
component does not need choice). Exact types and source hashes are
appended to the same accepted-components file, now six entries.

The actual ordinal recursion, antitonicity, image theorem below a kernel
cut, and literal quotient-map instance also passed the independent exact
gates and standard-three axiom audit in
`build-reports/1793251592919663407-2.json`. There are now nine accepted
component gates. This closes the entire first displayed conclusion of
`lem:quotient-filtration`, generalized to arbitrary cuts, while the full
two-conclusion numbered lemma remains pending.

Actual socles, successive-socle quotients, their constructed ZMod module
structures, and the actual induced map have been written in `UlmDefinitions`
and `UlmMapDefinitions`; they are not yet compiled. `UlmTargets` fixed
bijectivity before its theorem proof was written. Both that candidate and
the full omega-cut/rank candidate are now written but uncompiled, as detailed
in the pause handoff above.
`PGroups/PROOF-PLAN.md` separates this chain from the much larger
Scott/classification suppliers. No full numbered paper target has been
marked complete.

## Preserved differential work

The first candidate module is `Differential/Constants.lean`, written for the
characteristic-zero algebraic-constants lemma by the minimal polynomial,
its separability, and Mathlib's polynomial derivation chain rule.
The module is written but **not yet accepted by compilation**. The first
shared-runner attempt stopped safely at its 90-second wall limit while
loading/elaborating the fixed statement module, with peak process-tree
RSS 362,792 KiB and no Lean error output. The specification imports were
then reduced to definitions, and the spectral specification was split
out. That changed-import retry, and a subsequent explicit rational-algebra
import correction, also hit the 90-second wall limit. A separate graph
module did likewise. Finally, even the small semantics module importing
only `Mathlib.Order.Defs.PartialOrder` failed with an explicit managed-heap
exception after 23.433 seconds (heap cap 768 MiB; measured RSS 843,304 KiB).
This supplies a resource diagnosis rather than a mathematical rejection.
No actual RSS cap was raised. Root's controlled PartialOrder import probe
then passed in 10.856 seconds at 856,332 KiB RSS with a 1536-MiB managed
allocation budget and the unchanged 1024-MiB hard RSS/system-free guard.
The shared default has been adjusted based on that measured cause.
After the ordinal lane released its slot, the exact differential statement
gate also stopped at 90 seconds with the new managed budget, at 641,088 KiB
RSS and without a theorem diagnostic. Compilation is again on HOLD while
root tests an import-only baseline. No resource cap was raised by this lane.
No compiler is currently running for this lane.
All candidates are preserved and contain no admitted proof or added axiom.

A read-only inspection of the pinned Lean implementation found a further
concrete infrastructure distinction: `Lean.Elab.processHeaderCore` imports
private transitive module information for legacy files without `module`,
whereas batch files with `module` request exported information. The pinned
Mathlib uses the new module system; these initial project files used legacy
headers. `IMPORT-PROFILE.json` records static closure sizes, not a kernel
audit or a measured diagnosis. Root is testing a controlled modern-module
probe, which passed with `Mathlib.Data.Real.Basic` under the unchanged
physical safety caps. At root's instruction, all 24 owned Lean files now
use `module`, public imports and exposed public declarations.
`MODULE-MIGRATION.json` records the old/new source hashes and checksums of
the unchanged mathematical bodies; fixed-specification hashes were
refreshed while retaining their legacy hashes. Every migrated file still
requires fresh compilation except the exact `Differential/Targets.lean`,
which now passed in 83.638 seconds (4.11 observed CPU seconds; peak RSS
866,716 KiB). The same reserved batch then stopped `Constants.lean` at its
90.13-second wall guard, with 4.21 observed CPU seconds, peak RSS 966,780 KiB,
last wait channel `futex_do_wait`, and no Lean theorem diagnostic. The
compiler slot has been released and this lane is on HOLD pending root's
next resource decision. There is no passing differential candidate/gate.
No theorem statement was changed to avoid imports.

Root then separated the wall and CPU guards after the measured I/O/wait
behavior: wall allowance 180 seconds, CPU allowance still 90 seconds,
actual RSS cap still 1 GiB, prelaunch memory gate 1 GiB. The exact candidate
retry again stopped at the wall guard after 180.073 seconds, only 4.85
observed CPU seconds, 714,968 KiB peak RSS, and `futex_do_wait`, without any
Lean theorem diagnostic. Its source hash was unchanged. The compiler slot
was released to root; this lane will not retry absent a distinct measured
cause. A modern import-only probe of the exact derivation/separability
closure has been suggested to distinguish imports from elaboration.
After the queued peer gates released, that one agreed import-only probe
was deferred by the prelaunch memory guard (1,021 MiB available versus
1,024 MiB required). No compiler launched, no guard was lowered, and the
slot was left free for other work. After a substantial deferral, the
unchanged guard passed and the first actual import-only baseline launched.
It reproduced the wall stop at 180.113 seconds, 5.35 observed CPU seconds,
781,948 KiB peak RSS, and no `#check` output. This isolates the wait to the
actual import closure without any candidate theorem. The unchanged
Separable baseline will not be retried.

Root approved a separate same-target implementation using the minimal
polynomial's degree rather than the general separability framework.
`ConstantsMinpolyDegree.lean` and `MinpolyDegreeStatementChecks.lean`
are written, with the same frozen `Targets.lean` and no changed input
hypothesis. A zero derivative evaluation would make the minimal polynomial
divide its nonzero, smaller-degree derivative, a contradiction.
This alternative is also uncompiled; the original candidate is preserved.
Root has authorized one distinct-source native check of this alternative
after the repaired root RL gate, followed by the ordinal lane's queued
NormBalls check. That check also stopped without a Lean diagnostic at
180.113 seconds, 6.06 observed CPU seconds and 815,124 KiB peak RSS.
The unchanged alternative will not be retried. No cap increase occurred.

At root's instruction, native work now proceeds to the genuine forest
semantics: `Forests/OrderStatementChecks.lean` proves that incomparable
vertices have no common upper bound using the actual Mathlib partial
order and source forest predicate. This is separate from the raw `Core*`
drafts. The next contiguous target fixes width by all finite antichains
and leaves by actual maximal elements, then proves their cardinal bounds
coincide. Its independent `WidthTargets.lean` was registered before the
candidate proof. The candidate constructs maximal extensions and the
antichain injection, with neither used as an input supplier. These checks
passed after root's actual ultrafilter batch. Full JEP classification
and all other numbered paper targets remain pending.

The next differential candidate is distinct-weight algebraic independence.
Mathlib already proves linear independence of eigenvectors at distinct
eigenvalues. `SpectralIndependence.lean` includes candidate proofs for
derivatives of differential monomials, injectivity of the weight map
from rational linear independence, and injectivity of polynomial
evaluation. They are not accepted until compiled. Its fixed statement
is separate in `SpectralTargets.lean`, with an explicit statement gate.

Actual forest/comparability definitions, the finite multiplication-by-p
image calculation, and actual differential-polynomial jet evaluation are
also written. All remain explicitly uncompiled.

The existing generated-field dependency now also has actual semantics and
written candidates: `fieldGeneratedByJets` is the intermediate field adjoin
of the actual derivative sequence. Field-adjoin induction proves closure
under the ambient derivation, with the inverse rule included; derivative
induction proves minimality among closed intermediate fields containing the
element. A restricted derivation is constructed on that field. The three
fixed statements were registered before their proof candidates. They remain
uncompiled and do not imply either full constraint criterion.

Before the compiler hold, a raw-relation formulation of elementary
predecessor-chain facts was added under `Forests/Core*`. Its three fixed
comparison statements have candidate constructive proofs, but its runner
attempt returned BUSY without launching Lean. These files are preserved;
they are not being substituted for the actual Mathlib/paper targets.

The pinned Mathlib supplies finite-dimensional differential-field extensions
and uniqueness in `FieldTheory/Differential/Basic.lean`. This is a promising
proved supplier for the finite splitting-field analysis, rather than an
additional project axiom. Its use still requires the appropriate source
statement match and axiom audit.

`FiniteExtensionTargets.lean` now fixes the ordinary-derivation statement
that every finite-dimensional field extension has exactly one compatible
extended derivation. Its candidate constructs the relevant differential
structures and applies the actual proved Mathlib construction and uniqueness.
The statement was hashed before its candidate proof was written. The gate
remains uncompiled; neither an infinite-algebraic-extension theorem nor the
full spectral criterion is claimed from it.

`ModelsAlgebra/Differential/PROOF-PLAN.md` records the exact twelve-step
dependency chain for the two existing full criteria, including the actual
generated fields, curve kernel, generic witnesses, finite splitting-field
derivation, spectral descent and effective algorithms. There is no missing
supplier promoted to an assumption and no new target chosen.

## Build receipts

- `build-reports/1793242628864689750-2.json`: first differential statement
  module, safe wall stop.
- `build-reports/1793242943195721338-2.json`: reduced statement imports,
  safe wall stop.
- `build-reports/1793243125363443179-2.json`: explicit rational-algebra
  import and finite elaboration-heartbeat option, safe wall stop.
- `build-reports/1793243381201804573-2.json`: independent graph module,
  safe wall stop.
- `build-reports/1793243575344037901-2.json`: small Mathlib partial-order
  semantics, explicit managed-heap exhaustion.
- `build-reports/1793244775855059339-2.json`: exact differential statement
  gate with the adjusted managed budget, safe wall stop and no diagnostic.
- `build-reports/1793246030144261846-2.json`: modern exact statement module
  passed; subsequent minpoly candidate stopped safely at the wall guard.
- `build-reports/1793246557884919386-2.json`: unchanged exact candidate at
  the revised 180-second wall allowance, safe stop without a diagnostic.
- `build-reports/1793247750664080886-2.json`: first actual import-only
  Separable baseline, safe wall stop reproducing the wait without a proof.
- `build-reports/1793248193560190399-2.json`: distinct minpoly-degree
  implementation with the unchanged fixed target, safe wall stop.

The nine exact forest and p-filtration component gates above are accepted. No full
numbered paper target is yet complete in this lane.

## Full dependency obligations

For paper 15: algebraic constants; derivation extension; actual
differential-polynomial syntax/evaluation; differential generated fields;
the order-one function-field construction and designated-root
isomorphism; root/squarefree-divisibility criterion; exact positive and
negative constraint branches; spectral coordinates and independence;
generic/missing-coordinate differential fields; rational resultant and
effective polynomial algorithms; cyclotomic independence. The parent
constraint predicate will not be defined to mean either divisibility
criterion.

For paper 03: finite predecessor-chain posets, order embeddings and
induced comparability graphs; trivially-perfect representation and
isomorphism uniqueness; full embedding-existence transfer; Carter's
decision algorithm and its termination proof; bounded-host certificate
search; binary-tree cluster argument for width; countable age construction.
The cited Carter theorem is not a permissible final axiom.

For paper 01: countable infinitary syntax and Scott complexity;
transfinite p-filtration and Ulm invariants; countable reduced/divisible
decomposition; bounded classification; Ulm and prescribed-tail/Zippin
existence; the source back-and-forth theorem and both same-quotient
terminal-deletion comparisons; decreasing-sequence spectrum examples;
the infinite-divisible-rank argument and the all-group pure-Sigma
exclusion; the cited general infinitary-complexity restrictions. Existing
group and ordinal libraries do not by themselves constitute these proofs.

No modules from the 3.1.3 project have been copied or imported at this
checkpoint. Its ordinal/epistemic constructions have not yet supplied a
direct differential-field, Scott-analysis or Carter-algorithm dependency.
