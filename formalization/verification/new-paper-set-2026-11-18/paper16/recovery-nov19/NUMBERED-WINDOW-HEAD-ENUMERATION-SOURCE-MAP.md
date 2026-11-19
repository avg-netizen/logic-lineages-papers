# Finite actual head universe: source-first supporting comparator

Source: paper16 foundations' literal simple types/native constructors,
ordering's finite ranked signature and precedence, and ordinals lines
12–24 and 70–76. This is only the exact finite **head-symbol** universe
used by the later arithmetic argument. It does not claim finite primary
classes of complete terms, term codes, arithmetic accessibility, or ID1.

- `candidates` lists actual distinct head constructors only:
  zero/succ; case and recursor with their literal type argument from
  finite K; original binary application heads with both domain and
  codomain from K; and each actual fixed name/arity declaration in
  `Spine.Signature.entries`. Variables, bottom, and auxiliary
  applications are term constructors, not actual heads in this list.
- `headBit` uses actual `Spine.classRank` admission and checks
  membership of **every** type in the original
  `DecisionInventory.declaration f`, including original result,
  base-argument types and their subtypes for all head forms, even
  when a numbered head later has a different current output type.
  Completeness must establish that a case/recursor parameter appears
  in that actual result declaration, both app parameters in original
  declaration, and every admitted ranked head in the actual table.
  No hypothesis that the candidate parameter is put in K by hand.
- `unique` deduplicates by actual `Head` decidable equality, never
  by rank/class, so two distinct equivalent heads both remain.
  Both enumerators prove literal membership iff original guards and
  a duplicate-free list.
- `equivalentHeads` is the admitted list filtered by the actual same
  original `classRank`; a member implies that the given head itself
  has a class by matching a genuinely admitted member's rank. The
  characterization uses original `Spine.Equivalent`, not just name
  equality or equivalence of retyped current results. No selected
  class representative, alternative signature, context or syntax.

After independent scope and exact target-only native preflight, prove
actual signature lookup soundness, declaration parameter recovery,
literal candidate membership, bit correctness and filtered finite
equivalent enumeration. All scope depends on explicit original guards,
not on an unrelated generic finite-alphabet head domain.
