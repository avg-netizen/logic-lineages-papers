# Complete current19 lem:standard-residues

The comparator retains the complete printed lemma in decision-boundaries.tex: every positive modulus m (including m=1), every hierarchy level j>=1 and n>=m, and every unchanged standard-control input t>=max(0,m-100). Natural subtraction m-100 is exactly that threshold, not the weaker t>=m.

The witness is the fixed numerical function fastControlResidue m = fastControl 1 m % m, not an oracle or existential choice. Its range and actual Mathlib Primrec theorem make the source "one can compute" claim explicit. The canonical variable-seed hierarchy and Phi=F5(t+100) are unchanged literal source definitions. The witness is extensionally the source common residue once congruence/range are proved; no requirement to implement the explanatory CRT proof algorithm is added.

Candidate suppliers in ControlResidueProof prove genuine modulus/tower induction, positive-level stability and the exact shifted bound. Fresh current alias, native closure, axioms and final review required. This lemma has no bounded-machine H premise and no comparison/hardness/nonperiodicity conclusion; those separate obligations remain open. Parked paper20 tuple-period is not involved.
