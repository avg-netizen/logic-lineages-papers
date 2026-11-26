# Actual full-root interpolation support: frozen six-target scope

This supplies the missing polynomial completeness ingredient for current paper20
`thm:residue-observer`, not that theorem itself. Work over the actual splitting
field of the literal A_d over F2 and its COMPLETE distinct root set from the
previous frozen packet. No orbit subset, caller-supplied factorization, or
assumed partial-fraction representation is used.

Definitions are the literal monic full-root product T, the product D_z omitting
exactly one root, actual residues U(z)/D_z(z), and the actual finite Lagrange sum.
Six targets: exact degree/monicity of T; literal factor removal; D_z(z) nonzero;
strict omitted-product degree; evaluation of the actual sum at every root; and
polynomial equality for EVERY U of degree below the full root-set cardinality.
The zero polynomial and empty root set (d=0) are included via WithBot degree;
no nonzero-U or nonempty-root premise is added. Proof plan is direct product
evaluation plus polynomial root-count uniqueness, not a Vandermonde import.

Independent actual rational states still need a geometric/divisibility bridge:
canonical denominator divides T iff all geometric poles are among these roots
and simple (with properness separately required). Merely checking roots visible
in this finite field does NOT suffice to exclude an unrelated irreducible
factor. That bridge, actual rational partial-fraction completeness/descent,
operator/output intertwiners, all-word observer and effective enumeration remain
separate pending obligations. This packet does not define states as the range
of the proposed reconstruction and does not assume their completeness.
