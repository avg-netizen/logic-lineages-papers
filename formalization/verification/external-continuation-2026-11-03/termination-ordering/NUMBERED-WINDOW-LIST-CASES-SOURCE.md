# Restricted-window list and mark constructor suppliers

Source: paper06 arithmetic simulation and the five-way derivation induction.
The actual source syntax, packed occurrences, permutations, finite marking and
primitive replacement relation are unchanged. Only the output paths use the
already checked fixed-window relation.

The five certificate families quantify over every represented source at a
uniform finite label budget, then require actual initial source confinement and
literal target types/head confinement. These are not assumed paths, terminal
invariants, or hidden completion oracles. The six targets prove only empty and
cons matching, positive marking, empty and cons replacement, and the actual
multiset replacement constructor from their explicitly supplied induction
certificates. Repeated occurrences, nonempty removed lists, and multiple uses
of the same replacement witness are retained.

Strict marking must derive marked source confinement from successful finite
marking. List proofs must transport source and target confinement through the
actual memberships, splits and permutations. No subtype-closure premise is
needed for these constructor cases. No arbitrary RawStep trace lifting occurs.

Final five-way source induction, final ordinary source support discharge,
chosen-trace coverage, finite class enumeration and the whole simulation
statement remain pending. No new numbered source claim is completed here.
