# Fixed-window primary equivalence

Source: paper06 lines 551–556 describes primary equivalence restricted to the fixed auxiliary type universe, preserving shape, labels, result types and extra-list order while exchanging equivalent heads and appropriate base permutations.

WindowPrimary and WindowArgumentPrimary copy every original Primary/ArgumentPrimary generator. Only the ordinary/numbered head-exchange generators add membership of both exchanged heads in the already defined HeadInWindow arity symbols S. Both guards matter because symmetry must not introduce an unbounded native annotation. Original head equivalence, result equality when required, literal occurrence permutation, both auxiliary application congruences, binder and argument congruences, reflexivity, symmetry and transitivity remain unchanged. No endpoint confinement predicate is assumed.

The four targets prove erasure into the accepted unrestricted primary relations and equivalence of actual packed/argument confinement in both directions. Pure equivalence does not require subtype closure. Its application-argument congruence is zero-cost equivalence and does not add positive argument-side reduction.

This proves restricted primary generators and their confinement, not coverage of chosen simulation paths, a finite class enumerator, decidable equivalence, least-code representatives, arithmetic accessibility or full simulation. Root reviewed exact definitions and targets on 2026-11-03 before authoring.
