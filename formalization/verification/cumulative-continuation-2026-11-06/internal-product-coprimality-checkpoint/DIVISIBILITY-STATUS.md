# Actual coprimality from a unit certificate

Completed three new InternalDivisibility sources: Targets, Proof, StatementChecks. Frozen target is unchanged and compiled before proof authoring. Exact certificateCoprimality_exact has only propext, Classical.choice, Quot.sound.

The public certificateCoprimality theorem works under arbitrary contexts, arbitrary terms m,a,u,v, and derives the existing coprime m a from the literal equality succ(u*m)=v*a. No generator positivity assumption is required. The helper coprimeRename preserves the literal formula.

Proof mechanism: eliminate both common-divisor witnesses, factor both sides by the positive common divisor d=succ(e), and derive succ(K*d)=L*d. Object-calculus zero-or-successor splitting of e reduces to d=1 or d>=2. In the latter case, the checked internal remainder uniqueness supplier identifies residues 1 and 0, a contradiction. Thus every positive common divisor equals one directly (stronger than merely obtaining its divisibility of one). No semantic Nat reflection is used.

Final alias receipt: build-reports/1794003643204117431-6.json. Final proof receipt: build-reports/1794003631218047443-6.json. Peak observed RSS across this supplier's recorded checks: 1,198,476 KiB, under 1,536 MiB. Three failed candidates and all raw receipts/logs are retained. Repairs were ambiguous abbreviation/name resolution, equality embedding, and successor renaming only. Targets unchanged.

Also compiled the bounded worker's Definitions and Targets before proof authoring: build-reports/1794003651440043699-5.json. No bounded-family proof claim is made here.

Compiler slot returned to parent; no jobs running. Existing accepted sources untouched. No commits or publication. Parent owns recursive dependency closure, independent review, and overall checkpoint assembly.
