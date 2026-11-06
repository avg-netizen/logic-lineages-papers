# Original beta division steps: checked supporting component

Three exact internal statements now have derivations in the original calculus:
1. A dividend below the original beta modulus is represented with itself as
   remainder; the proof supplies quotient zero.
2. Every original beta instance implies its original strict remainder bound.
3. Given an original beta instance and the explicit condition that the
   successor remainder is still below the modulus, the successor dividend
   has the successor remainder.

The same quotient is retained in the third result. This does not cover
wraparound when the successor remainder equals the modulus, and does not
prove general division existence, beta functionality or sequence coding.
The predecessor/discreteness split and wraparound arithmetic remain future
steps toward the induction.

All three frozen exact aliases compile using only propext, Classical.choice
and Quot.sound. The final main proof/checks have no warnings. Exact source
receipt matching covers 750 current modules; peak across cited receipts is
1,226,832 KiB. The unchanged checker used one thread, 2,048 MiB heap,
1,536 MiB RSS and 2,048 MiB minimum free. No full-root or remote-CI claim.

Syntax repair history and raw logs are preserved in syntax-candidates;
main candidates preserve the embedding repair and subsequent warning cleanup.
Original target, calculus, arithmetic, beta and order definitions are
unchanged. Register unchanged at 167 checked, 2 inherited, 20 pending.
II5 is excluded; C_tau closure and whole ID1 are not established.

Independent read-only review accepted exact targets, original semantics,
final receipts, standard axiom aliases and preserved repairs. The author
separately verified the full focused source-to-receipt closure.
