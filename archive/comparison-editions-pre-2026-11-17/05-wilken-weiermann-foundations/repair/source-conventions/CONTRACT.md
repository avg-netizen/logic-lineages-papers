# Literal source conventions: repair contract

This is a mathematical source repair of paper 05, not a new comparison
algorithm, a resumption of the research frontier, or a Lean result. The
canonical manuscript is edited separately by the integrating author.

The primary source is Wilken–Weiermann, *Derivation lengths classification of
Gödel's T extending Howard's assignment*, arXiv:1203.0115v2 / LMCS 8(1:19),
2012. Definitions 2.1, 2.6, 2.9, 2.10, 2.18 and 3.1 distinguish literal
ordinal syntax from its ordinal interpretation. Finite sum association and
the treatment of out-of-range zero coordinates are not fixed at the AST
level by those definitions. Application of lambda terms being left associated
does not fix association of ordinal sums.

The repair must pay the following statements.

1. An explicit family of finite binary macro-expansion policies makes every
   generated coordinate, partial and zero-history assignment well defined.
   It preserves existing subtrees, the whole-free-first test, typed levels
   and the source's primitive exponential/product and collapse constructors.
   Actual padding is distinguished from an actual zero subtree.
2. For every such policy, partials and abstractions preserve their published
   graded domains. A corrected weak form of printed Lemma 2.19 is sufficient;
   its stated strict form is false already at the tracked scalar variable.
   The bounded-norm result is proved without that false strict inequality.
3. The actual-source forward translation and the two positive-coordinate
   classes stated in foundations.tex hold for each policy, with exactly the
   original original-T / ground-free-name restrictions. They do not identify
   assignments from different policies.
4. A literal, closed, well-typed original source has different assigned
   values under two permitted association policies. Therefore no proof may
   replace the missing convention by a claim of generated-source invariance.

The policies are faithful explicit readings of the printed formulas. No
claim identifies one as the uniquely intended historical convention. This
repair does not assert that fixed zero-history assignments decrease under
all reductions: the published termination proof uses history-dependent
assignment derivations. It does not purport to reprove all quantitative
bounds in the source appendix.

No source or accepted formalization freeze is changed. A bounded executable
control, when present, checks the named concrete witness only; the proofs,
not a finite test, establish the uniform statements.
