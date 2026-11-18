# Exact arithmetic undecidability audit

## Finding

No valid undecidability reduction or contradiction was found. The suspected inference from nonlinear growth or a unary exponential function to undecidability is invalid. This is distinct from the genuine unpaid Lean formalization of arbitrary quantifier alternation. No theorem/source/target has been changed by this audit.

## Exact manuscript structure

control.tex m:eq:f defines F0(n)=2^n, F(j+1)(n)=Fj iterated n+1 times from n, and f(n)=F5(n+100). m:thm:snyatkov claims decidability of Th(N;0,1,+,<,f), with exactly that fixed unary f. It does NOT add multiplication, BIT, a variable-modulus divisibility relation, arbitrary computable functions, or variable-seed iteration. The auxiliary H in its proof is fixed-seed: H(0)=1,H(n+1)=f(H(n)); it is not identified with the varying-start Fj hierarchy.

certified-fragments.tex m:thm:common preserves raw free names and pointwise truth on positive valuations, then claims arbitrary Boolean/quantified combinations. Its A0 uses natural constants, positive raw variables, addition and fixed nesting of f. At positive layers only common-head sums plus a closed constant are admitted, not an independent open remainder. m:thm:balanced similarly has one shared finite recursively certified basis, every head argument includes every basis entry positively, and dependent/repeated entries remain correlated. Neither claims arbitrary comparison of unrestricted ordinal functions.

## Primary-source check

Downloaded the exact cited [Snyatkov2008 paper](https://eprints.tversu.ru/id/eprint/494/1/19950136_2008_2_snyatkov.pdf), then visually read printed pages40,50,51 (text extraction has a broken font map). Page40 requires modular periodicity, strict increase and uniform shifted domination for each unbounded finite integer combination of translates; effectivity means computing the constants. Its hyperfunction starts at a fixed constant. Theorem2 and effective Corollary2 state quantifier elimination after adjoining divisibility and floor inverses, under the corresponding compatibility and hyperfunction-periodicity assumptions. This is genuinely an arbitrary-formula result, not existential-only. The manuscript's chosen route matches those stated hypotheses; its residue/growth argument and H last-iterate argument address them. This checks the cited theorem statement and domain match, not every detail of Snyatkov's proof.

[Benedikt–Chistikov–Mansutti, ICALP2023](https://drops.dagstuhl.de/storage/00lipics/lipics-vol261-icalp2023/LIPIcs.ICALP.2023.112/LIPIcs.ICALP.2023.112.pdf), abstract and introduction, explicitly distinguish decidable Presburger arithmetic with one unary power function from richer undecidable expansions. Thus unary exponential growth alone is not a counterexample. Their result is not itself a proof for this particular F5 control.

## Consequence for work

Continue treating full alternating nonlinear elimination as an unpaid constructive formalization dependency, not as a demonstrated false source claim. A valid negative result would need an actual interpretation of an undecidable structure in this precise fixed-f language; none has been supplied. Conversely, do not claim Lean completion just because the published theorem matches: its effective elimination theorem must be formalized or legitimately imported as a proved theorem, never inserted as an axiom or caller-supplied oracle.
