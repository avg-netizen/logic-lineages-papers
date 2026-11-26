# Current18 complete growth and effective residues

Source sections/control.tex m:lem:growth and m:lem:residues, every clause.
Literal fastControl0(n)=2^n and fastControl(j+1)(n)=fastControl(j)^[n+1](n);
Phi(n)=fastControl5(n+100). No fixed-seed substitution or changed shift.

Growth: every level is genuinely Computable, strictly increasing, dominates
2^n at all inputs; successor-level successor-input exponential gap; and
(A+2)*Phi(z)<=Phi(z+1) for all natural A<=z, including zero.

Residues: fixed explicit witness fastControlResidue(m)=fastControl1(m)%m,
proved Primrec (stronger than requested computable) and <m for positive m.
Every j>=1,n>=m has that common residue. Shifted Phi threshold is natural
subtraction m-100, exactly max(0,m-100). All s>=1,j>=2 with m<=2^(2^s)
have that residue; final all-u envelope m<=2^(2^Phi(u)) gives Phi(u+1)'s
residue. m=1 is included; m=0 is excluded exactly as printed.

The printed proof uses recursive CRT to exhibit the residue. The actual
explicit witness is source-equivalent: since the asserted common residue
already applies at F1(m), its unique representative in [0,m) must be
F1(m)%m. Existing tower-residue proof pays actual modular arithmetic; no CRT
or residue oracle is supplied. No advertised optimized evaluation bound.

Exact suppliers fullFastControlHierarchyGrowth and
fullFastControlConstantResidues have these expanded types. Revalidation
requires full native recursive evidence and independent final review.
These are genuine arithmetic hypotheses, not the full Snyatkov theorem: no
quantifier elimination, common/balanced quantified decision, or source
comparison is promoted by proving them.
