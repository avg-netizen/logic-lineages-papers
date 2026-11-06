# Accepted local least-number certificate

The original frozen **ActualLeastNumber** target is proved. For every arbitrary ordinary arithmetic formula P with parameter names α, and every original positive ID1 body, the existing internal calculus derives:

(∃x P(x)) → ∃x (P(x) ∧ ∀y (y < x → ¬P(y))).

The strict order is literally the existing OrdinaryArithmetic.lessFormula, not a new relation. The outer singleton binds x; the inner singleton binds y; α names remain free. No semantic Nat reflection, premise certificate, new axiom, sorry, admit, or native_decide occurs. The generic proof actually permits formulas from the expanded language; the checked original ordinary-language alias has exactly the frozen type.

Two additional unconditional suppliers are checked: s < succ t → (s < t ∨ s = t), and ¬(s < 0). Their proofs use original PA arithmetic constructors and induction on the additive witness. The least-number proof assumes absence of a minimum and derives the bounded exclusion invariant ∀y < x, ¬P(y) by original PA induction. The successor step uses the split and excludes P(x), since P(x) plus the invariant would produce a minimum. Existential elimination then contradicts an arbitrary witness of P. All logical steps are actual InternalCalculus.Derivation constructors, including the original classical rule.

## Verification

- Frozen definitions and targets: FROZEN.json, unchanged since before proof authoring.
- Final source hashes: SOURCE-HASHES.json (five new Lean files).
- Supplier-only initial successful gate: native/1794001390903093593-6.json.
- Final syntax successful gate: native/1794001594433739635-7.json (syntax passed; later proof then failed and was repaired).
- Final proof and exact-check successful gate: native/1794001652439411416-7.json.
- Exact aliases: leastNumber_exact, split_exact, zero_exact. All report precisely [propext, Quot.sound].
- Maximum observed process-tree RSS over this lane's receipts: 1,202,236 KiB, below unchanged 1,536 MiB cap. Sole compiler slot, one thread; check.py with heap 2048 MiB, RSS 1536 MiB, free floor 2048 MiB.
- Failed candidates and receipts are retained. candidates/06 reconstructs the exact failed intermediate source and its receipt hash was verified. No existing Lean source was changed.

This completes the least-number supplier, **not** Bezout, CRT, beta finite-sequence coding, the internal level-two consumer, or a numbered paper statement. Independent review accepted all five source files, the three exact aliases, original binding/calculus semantics, unchanged frozen targets and the retained repair sequence. The coordinator recursively matched all 766 focused source modules to retained successful receipts at durable evidence paths. Peak across cited receipts is 1,226,832 KiB. This is not a fresh full dependency rebuild. No full-root build or remote-CI success is claimed. Publication is handled separately by the coordinator. The compiler is finished and the sole slot is released.
