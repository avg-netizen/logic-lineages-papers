# Internal multiplication left successor

Accepted supporting lemma: for every body, variable type, and terms s and t, the original calculus derives the embedded equality (succ s) * t = s * t + t. The derivation-level supplier works under arbitrary Gamma.

The target was frozen and compiled before proof authoring. The proof uses original PA induction on t, multiplication recursion, and internal addition associativity and commutativity. No semantic reflection, added premise, or shortcut is used. The exact statement alias passed and its actual axiom closure is [propext, Quot.sound]. All compilation passed on the first attempt; there are no failed snapshots.

Native checks used scripts/check.py with memory-mib 2048, rss-mib 1536, min-free-mib 2048 and the existing pinned Lean 4.32.0-rc1 PATH. All receipts and terminal logs are retained here. The parent beta boundary target was also compiled successfully during this sole compiler slot. The slot has been released with no live native process. No commit or publication was attempted. This supporting lemma alone is not a complete beta boundary or paper theorem.
