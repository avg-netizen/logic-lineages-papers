# Comparator/bridge foundations: thirteen checked endpoints

Final native receipt `1794980097386911817-2`; read-only recursive verifier
reconciles 23 modules and 13 exact aliases with zero errors. Axioms are only
propext/Quot.sound. Original fixed core limits unchanged. Frozen definitions
and targets remain those approved after the explicit Nat annotation preflight.

Checked: fixed ranked arity; literal native equivalence and precedence above
application; admitted ranked precedence above native; positional removal/split
length laws; exact named-to-DB typing equivalence under every actual typed-name
binder environment; decoding typing; exact independent named/DB signature
validity; closed typed scoping; actual one-binder opening typing; constructive
common fresh-name existence; scoped decode-to-encode roundtrip.

The roundtrip does not assume the conclusion: it proves lookup at an index in
a distinct environment, extracts named binders from scoped type lookup, and
maintains a freshness condition excluding ambient binder names from free
occurrences. Decoding chooses a name above all ambient and free numeric names,
which proves the strengthened environment conditions beneath each binder.

One proof-only repair followed failed receipt `1794980086014349415-2`: ordinary
simp normalization of reflexive equality/if in lookupType instead of an overly
restricted simp-only list. Failed proof source retained. No target weakening.

Remaining bridge endpoints: EncodeRespectsAlpha, DecodeEncodeAlpha, AlphaExact,
OpeningBridge. Remaining elementary targets: weak/strict target ordinariness,
strict inclusion, ordinary reflexivity. No full alpha characterization,
comparison derivation transport, numbered manuscript theorem, root build or CI
claim follows from these foundation checks.
