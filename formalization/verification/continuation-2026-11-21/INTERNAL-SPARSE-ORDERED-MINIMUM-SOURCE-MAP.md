# Paper 16: physical minimum of a supplied original ordered raw pool

This is the local minimum prerequisite only. The printed source uses
finite least-code representatives (ordinals.tex lines 70–77).
`NumberedWindowScalarAlgorithm.least` delegates to
`NumberedWindowClassAlgorithm.least` at the actual directed edge, ordered
vertices, and seed. The last operation there is exactly
`(members edge vertices seed).min?`. This packet implements that last
operation on a supplied original ordered sparse list. It does not select
vertices, perform initial/advance filters, choose round fuel, assert class
membership, or identify an old least program by extensional equality.

## Raw input, scratch representation, result

 * Input is one original raw executable `NumberedWindowFieldAlgorithm`
   list code, including empty and malformed codes/tails; the original raw
   cell constructor is the sparse polynomial pair plus one.
 * `orderedPoolMinimum` calls the actual checked `parser` from the sparse
   field parser. Its accepted all-input numerical contract is
   `ActualEncodedOutput`: zero on any malformed raw list and
   `numbersNumber xs + 1` on successful `unpack raw = some xs`.
   `numbersNumber` is the standard Nat.pair ordered scratch encoding; it
   does not sort, deduplicate, or change any original field number.
   Division between sparse raw and standard scratch encodings is explicit.
 * The actual zero parser branch returns zero, not a fabricated empty
   list. Otherwise the physical predecessor selects the actual scratch
   code and calls `scratchMinimum`. The admitted memo-table
   `InternalRawListRecursion.listRec` for standard scratch traverses the
   unchanged decoded list by a right fold at zero parameter count.
 * For head h and encoded tail minimum r, `minimumStep` takes the
   successor of h if r=0; otherwise it compares those two actual encoded
   numbers using the existing physical less-than program. It returns
   successor h on a strict comparison hit and r on a miss (including
   ties). A list is never materialized with deleted occurrences.
   The nil base is zero; a real minimum 0 is represented by 1.
 * `ExactAllInputOrderedPoolMinimum` is exactly
   `evaluate orderedPoolMinimum [raw] = encodeState ((unpack raw).bind List.min?)`.
   No admitted pool, successful parse, distinctness, or ordered-by-value
   premise appears. Intended proof uses checked 628 numeric parser,
   `numbersRoundTrip`, actual list-recursion evaluation, exact
   physical less-than/branch equations, and elementary
   `List.min?`/right-fold recursion. None has been authored here.

## Exact first local object obligations

`ExactOpenOrderedMinimumStep` concerns arbitrary ordinary h/prior/k
in an arbitrary fixed positive body and proof context. A success
`programGraph minimumStep (S k) [h,prior]` yields the genuine ordinary
disjunction `k=h` or `prior=S k`. The intended argument opens actual graph
values and branches using real internal program and successor cases, then
uses exact output functionality and successor cancellation. It does not
reflect or assume numerical least calibration.

`ExactOpenScratchMinimumCons` pays an actual one-cell provenance step for
the same chosen `scratchMinimum`: on a genuine supplied standard
`consCode code [h,t]` graph and successful minimum of that very code,
the selected code equals h or the same successful minimum graph holds at
the same actual tail t. The original `ActualOriginalListRecursionCons`
supplies an internal existential naming the exact tail result; discharging
the option-step disjunction uses its equation to transport the actual
tail graph output. No guessed numeric tail, member test, or arbitrary
decoded-list input is inserted. This is not full induction to an index
or an occurrence of the complete original raw input. The separate open
raw-parser to scratch graph assembly, unbounded occurrences, and original
directed-round provenance will still require explicit proof.

There is no old least transport, output scalar admission, source validity
or ValidWindow premise, least-self/coherence inference, committed raw matching
or numbered accessibility conclusion. Records 683/687 supply only the
already established external actual rounds/ordered-pool background.
