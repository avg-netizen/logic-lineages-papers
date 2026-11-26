# Literal mark-decrease and supplied primitive replacement certificates

Supporting scope only for ordinals.tex 47–49, 60–68, 70–76 and
174–177, in the fixed numerical-window development. This does not
prove numbered lem:arithmetic-accessibility, full raw-step
effectivity, R_S, object-level arithmetic, or ID_1.

The existing NumberedWindowRules.MarkDecrease and
PrimitiveReplacement are independently defined relations. The new
comparator must reflect them, not redefine either. The mark bit:

- Ordinary to finite retains the literal head, every ordered original
  base occurrence, original result annotation, and requires no extras.
  Every finite label, including zero, is allowed in the target.
- Finite to finite checks strict natural ordering of the labels, same
  literal head/current output type, identical ordered base and extras.
  In particular finite zero has no smaller label.
- The common initial lambda case checks the literal binder annotation
  and recurses only into the two bodies. It has no variable, bottom,
  application, or nested argument case.

For known ReplacementWitness lists, the checker reflects exactly
the original kept/removed/added matrix. Both source-to-(kept++removed)
and target-to-(kept++added) permutations use accepted literal raw
syntax equality, retaining duplicate occurrences. Removed must be
nonempty, each added occurrence must have a removed dominator with the
original literal mark decrease, and added may be empty (deletion).
A removed occurrence may dominate more than one added occurrence, as
in the source. Existential calibration gives a supplied witness iff
the original relation; the algorithm neither searches for nor decides
existential partitions. No new scope guard is added to these raw
certificate checks. Window typing is a separate already accepted
premise of actual steps; genuine admitted positive mark paths were
accepted as packet440. Ranked comparison and all raw rule certificates
are separately staged work.
