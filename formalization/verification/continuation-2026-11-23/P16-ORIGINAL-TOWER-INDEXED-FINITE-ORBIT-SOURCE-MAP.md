# Paper 16: finite approximants below the literal indexed tower entry

Source correspondence: `16-persistent-marking-termination-ordering/sections/ordinals.tex`
(line 467 onward, native iteration argument at the indexed carrier; lines
513–554, literal fix, higher-type extractors and terminal zero; lines 569–590,
literal tower). The existing exact tower-entry proof (acceptance #1492) gives
the printed term `t_(l+2)` and its typed reduction/strict chain to
`indexedW .base (innerMap l) (s t₀) omegaCarrier`.

* `NativeIndexedCarrierFiniteOrbitProof` gives an exact original
  typed carrier fact at any actual finite type. `K A P i` selects the
  original `P`; the checked native carrier absorbs (P v) when (v) is in
  its strict lower cone, using precisely the included-support component
  of that same native strict edge. Ordinary induction repeats it any
  finite number of times. The seed is in that cone, and the original
  indexed theorem also gives the exact starting edge from a checked
  strictly earlier indexed carrier. There is no universal argument or
  congruence closure assumption.
* `NativeTowerIndexedFiniteOrbitProof` consumes the exact original
  tower-entry proof with the same substituted `innerMap l` and seed
  `s t₀`. It composes the strictly positive original run and proves that
  `t_(l+2)` lies above all finite orbits of this same map, both on its
  original seed and on each exact earlier indexed carrier. The last
  clause specializes earlier indices to the genuine finite iterates of
  original s on Z below the original omega cap, using #503. It retains
  the actual entry run and literal source equalities.

No claim compares two finite approximants with each other, supplies a
countable limit realization, proves the printed finite-type iteration theorem,
or proves Simmons helpfulness, (R), cofinality, or a height. Only actual
native terms and the existing confined NativeBelow relation are used:
neither root imports the ordinal library or the mixed realization files.
