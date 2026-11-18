# Correcting the strict scalar lemma without changing the norm multiplier

Notation is that of the source. P_i^X denotes its partial δ_i^x, while
δ^X denotes the assembled vector. The source's natural sums/products are
written with +/· here. All inequalities of expressions mean pointwise
inequalities under every admissible substitution. N denotes the source
additive norm, not AST size. The tracked vector has level k and n=k+1≥1.
Every actual C_i^X expression is positive; C_0^X expressions have finite
positive values. Vectors called bounded below have N(h_i)≤h_0 at every
positive coordinate and every admissible substitution.

## 1. The printed strict assertion is false

Printed page22, Lemma2.19 of the 2012 primary PDF states

    h{X:=1} < (P_0^X h)_0     for h∈C_0^X.

The literal tracked scalar variable h=x_0 belongs to C_0^X. The two sides
are both One, by Definition2.18. Hence the asserted strict inequality is
false. This has been checked against the actual publisher PDF, not only
an extracted `<` glyph. Its SHA256 and source locator are recorded in
SOURCES.json. The assertion's strictness is not a harmless convention
choice. It fails for every policy in POLICY-AND-TRANSLATION.md.

The source's strict auxiliary estimate (A.5), page36, can also fail. Take
k=0, n=1 and h=(x_0,1), a bounded-norm vector. For i=1 the maximal X-free
subterm t=1 has norm one and `(P_0 h_0)_0=1`, so (A.5) claims `1<1`.
The non-strict version of (A.5) is valid, but by itself does not pay an
extra diagonal `+1`. The proof below pays that extra unit another way.

Neither observation refutes the source's termination result. We retain
the counterexamples visibly and replace the invalid supplier.

## 2. Weak scalar replacement and domain closure

**Theorem W.** For every h∈C_0^X,

    h{X:=1} ≤ (P_0^X h)_0.

Furthermore every P_i^X h is a valid X-free C-vector of level n, and every
δ^X h is a valid X-free C-vector of level max(n,lv(h)). These statements
hold for every admissible binary macro-expansion policy.

Proof. Use simultaneous structural induction on the grammar derivation
and the partial clauses. A whole-X-free scalar h has scalar partial h+1.
The tracked variable x_0 has both sides one. An active sum has scalar
partial P(f)+P(g)+1, so the two weak induction hypotheses suffice.

For an active collapse h=Psi(f,g), its scalar partial is

    ψ(ω·f{X:=1} + (P_0^X g)_0).

The two heads are identical after X:=1 and the finite tails satisfy the
weak induction hypothesis. For fixed ordinal a and finite u≤v,
Proposition2.3(1) gives ψ(a+u)≤ψ(a+v); equivalently iterate its finite-tail
inequality ψ(β)+r≤ψ(β+r). Here ω·f{X:=1} is a nonzero limit, so its natural
sum with a finite tail agrees with the displayed ordinary finite tail.
This proves W without claiming general monotonicity of ψ.

The same induction pays domain closure, including this collapse case.
By its original grammar premise and admissibility of the all-ones vector,

    N(f{X:=1}) ≤ F_2(g{X:=1}) ≤ F_2((P_0^X g)_0).

The last step uses W and monotonicity of F_2. Thus the new collapse has
exactly the C_0 domain premise it needs. Its head has the correct positive
grade. Whole-free diagonal outputs h+1 and all off-diagonal Ones belong
to their indicated classes; at grade i>n there is no diagonal output.
The tracked-variable case is constant. Active sum and exponential
partials only sum appropriate already constructed coordinates, including
two unchanged copies in the latter. The positive collapse outputs sum
the positive-head partial and the scalar-tail positive partial.
All these outputs are X-free. The assembled finite positive sums and
the positive integer repeat at zero remain in their classes. For i>n
an original h_i is already X-free, since the tracked vector has no such
component and promotion from C_0 to a positive C_i^X requires X-freeness.
These higher coordinates are simply retained. ∎

## 3. A positive-grade free-subterm bound

Fix any admissible substitution for the names other than X. Substitute
ones for X in the input vector, and write

    B=h_0{X:=1},       H=(P_0^X h_0)_0.

For a bounded input, B≥1, H≥B by W, and every input coordinate satisfies
N(h_i{X:=1})≤B (also at i=0, since that coordinate is finite).

In a partial recursion, stop a path at the *first* wholly X-free subtree.
The free subtrees encountered at a **positive** grammar grade, from any
coordinate of h, satisfy the sharper bound

    N(t) ≤ 2^{n-1} B.                                      (P)

Proof. A descent through an active sum or through an exponential's tail
does not increase norm. A descent through an active positive-grade
exponential's head increases the grade by one and costs at most a factor
two, by Proposition2.2:

    N(f) ≤ 2N(2^f) ≤ 2N(2^f·g).

The latter inequality uses positivity of g and the lower natural-product
norm bound. Once grade n=k+1 has been reached, the entire subtree is
X-free and the path stops. From a positive root of grade i≥1 there are
therefore at most max(n-i,0) such head steps, at most n-1. A root with
i>n is already X-free.

A root at grade zero can enter a positive grade only through a collapse
head. That step costs no factor two. Indeed for a closed admissible
instance ψ(ω·f+g), positivity and Propositions2.2/2.3 give

    N(f) ≤ N(ω·f+g) ≤ ψ(ω·f+g),
    g ≤ ψ(ω·f+g).

The first step enters grade one. There are at most n-1 subsequent active
exponential-head steps before X-freeness forces a stop. A scalar tail
remains at grade zero and never contains an active exponential. All
norms in this path argument may be computed after X:=1: a maximal
X-free t is unchanged, and the parent bounds hold at that admissible
instance. Starting from a coordinate norm at most B proves (P).

No descent through a positive-grade promoted scalar causes an extra
case: the C_i^X promotion premise makes that whole scalar X-free, so
the partial recursion stops there. ∎

This argument also reproves the source's weaker path bound with multiplier
2^{n dotminus i}, and hence the corrected non-strict (A.5). The sharper
positive-grade bound (P) is what pays the necessary diagonal increment.

## 4. The original bounded-norm multiplier still suffices

**Theorem N.** If h∈C^X has bounded norm, then δ^X h has bounded norm,
with the unchanged printed multiplier

    S_X(h)=2^n Σ_{i=0}^{lv(h)} s_X(h_i).

Proof. Continue with B,H above and put ν=2^n H. Every positive-grade
free subtree t that can be copied at a positive diagonal partial output
satisfies

    N(t)+1 ≤ 2^{n-1}B+1 ≤ 2^n H = ν.

Here 2^{n-1}B≥1. A free scalar subtree is *not* copied into a positive
output: its positive outputs are Ones. Thus the distinction between
scalar and positive-grade free subtrees is essential.

Induct on each partial recursion inside the input vector, for any
positive output j≤n. We claim

    N((P_i^X h_i)_j) ≤ s_X(h_i) ν.                         (N1)

At a whole-free positive input, the only possible copied output is t+1,
whose norm is at most ν by the preceding paragraph; other outputs are
One. At a whole-free scalar or a tracked variable every positive output
is One. An active sum has norm at most

    (s_X(f)+s_X(g))ν + 1 ≤ (s_X(f)+s_X(g)+1)ν.

An active exponential's partial output is a sum of two head-partial
copies, one tail partial and One. Its norm is at most
`(2s_X(f)+s_X(g)+1)ν`. A scalar collapse's positive output sums the
head and tail partials, with bound `(s_X(f)+s_X(g))ν`, which is no
larger than the required size bound. Additivity of N makes these arguments
valid for every binary association policy. This proves (N1), which is
the source's (A.6), now with a valid proof.

For 0<j≤n, sum (N1) over actual i. Since δ_0 is the finite positive
integer S_X(h)·H, this gives

    N((δ^X h)_j) ≤ (Σ_i s_X(h_i))·2^n H = (δ^X h)_0.

For j>n, h_j is wholly X-free and is unchanged by X:=1. Hence

    N((δ^X h)_j)=N(h_j)≤B≤H≤(δ^X h)_0.

The proof held at every arbitrary admissible substitution of the other
names, establishing the required universal bounded norm. ∎

The proof does not increase the constant, modify the assignment, use an
unproved strict variant of W, or assume whole-tree representation
invariance. It uses the same actual source constructors and multiplier.

## 5. Audit of the printed uses of Lemma2.19

The inspected primary text explicitly invokes Lemma2.19 in the following
places; these are separate from a claim of auditing the whole source.

* Immediately below the lemma, page22, its use is domain closure for a
  new scalar collapse. The weak chain in TheoremW pays it directly.
* AppendixA.2, page36, uses strictness to obtain (A.5). That printed
  estimate is false as shown above. TheoremN proves the needed (A.6)
  and bounded-norm conclusion by the sharper positive-grade bound (P),
  without retaining the false strict estimate.
* AppendixA.2, page37, uses strictness for coordinates j>n. Only a weak
  bound is required; the displayed chain B≤H≤δ_0 proves it.
* AppendixA.7(2), page41, uses the strict link
  `F_2(ḡ)<F_2((P_0g)_0)` in the active-collapse case. Replace it by a
  weak link using W. If `Q=ψ(ω·s_X(g)·α+s_X(g)·m)` is the strict
  upper bound on `(P_0g)_0` supplied by that proof's induction hypothesis,
  the chain needed for the next comparison is still

      N(f̄) ≤ F_2(ḡ) ≤ F_2((P_0g)_0) < F_2(Q).

  Thus the required strict slack is supplied by the *upper-bound induction
  hypothesis*, not by the false scalar lemma. The separate strict head
  comparison f̄<α in A.7(2) is unchanged. This is a repair of that local
  use, not a fresh assertion that every other line of A.7 was checked.

The source's beta supplier, Lemma2.22 / AppendixA.3, concerns
`h < (P_i^X h □ X)_i`. This is different from W: the box and the extra
input X make its variable case strict. Its displayed structural proof
does not explicitly invoke the false Lemma2.19; its partial-domain and
bounded-norm prerequisites are paid above. No claim that the corrected
W is strict is made when citing that separate beta statement.

The exact continuation of a proof of all original quantitative derivation
bounds would still have to retain their stated assumptions and inspect
their other suppliers. Paper05's pointwise translation needs the domain
and bounded-norm assertions proved here, not an unchecked wholesale
upgrade of all those quantitative corollaries.
