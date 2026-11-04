# Next full paper08 endpoint: uniform kernel separation

Status: bounded source/contract analysis for root review. No new target, proof,
manuscript change or numbered promotion is made here. The six accepted S4 Lean
files and their evidence pins remain immutable.

Current corrected paper08 SHA256:
7463df840be926a243439d6a2ba969d58665c7a2a66345444eb8296505332c9a.
The three source repairs adopted in ROOT-SOURCE-ADOPTION.json remain accepted.

## Why this endpoint next

The complete pending lem:uniform is the next independent S4 source endpoint.
Its quantitative same-input mass separation and cross-input separation are
used by the ranked cancellation/ordered-guard language. It neither rebuilds
S3's arithmetic elimination nor S5's hardness reductions. Existing exact
quadratic V separation and principal-kernel mass/input programs are paid;
they should be reused. There is no accepted arbitrary-rank proof of the full
source region, so this is substantial mathematics, not another counter
assembly exercise.

## Exact domain boundary

The source region is

    d>=3, t>=T_d,
    f(t)>=C_d*(c+e+|j|+|k|+R+1),
    C_d=1000*d^2, T_3=16,
    T_d=max(T_(d-1),100*C_(d-1)+100*d) for d>=4.

It does NOT imply t>=c+d+1 or t>=e+d+1. For example, d=3, t=16,
c=20, e=0, j=k=0 and R=0 obey the region: f(16)>=2^116>189000,
but c+d+1=24>16. This is an arithmetic witness to a missing input-domain
implication, not a checked count/order counterexample.

The corrected source currently explicitly requires t>=c+d+1 in its kernel
definition. The accepted companion has padded initial suffix

    I = omega^d + max(t-c-(d+1),0),
    c+N(I) = max(t,c+d+1).

If c>t, its compensated first budget is f(c+d+1)-c, while the independent
principal-start source schedule spends f(t)-c. The first arguments of f
are strictly different. The existing SourceProcessBridge assumes the genuine
domain and cannot transfer the full displayed region. No broad-region
equality follows from its successful gate.

## Option A: keep the full numerical region

Keep the literal C_d/T_d region and prove separation for the independently
defined principal-start source process, including when c>t. This requires
an explicit source-domain extension/clarification: define the numerical
principal-start process whenever c<=f(t), and reserve t>=c+d+1 for genuine
prefix/companion correspondence. Describe t as the initial control input;
its first replacement has total norm f(t), even if the initial unpadded
principal plus numerical mass does not have norm t.

This is an explicit extension of the newly corrected source domain. It is
not a reinterpretation of actualSuffixKernelCount outside its valid input
domain. All already adopted fixed-parameter tail statements retain their
existing stronger tails, so their proved contracts and accepted bytes need
no change. The full uniform region guarantees c<=f(t) and e<=f(t).

The first new calibration obligation would be:

    d>=1, c<=f(t), Q=M(omega^d,f(t)-c)
    imply c+N(Q)=f(t), and
    sourceCount(d,c,t)=1+actualControlledCount(compensatedPrefixControl c,Q).

It must also give the exact original-schedule trace from replacement one
through finite exit. This is a theorem to prove, not a supplier premise.
Limit-part saturation pays the first norm equation. Subsequent total norms
are f^[i](t), so the compensated process AFTER Q has the same budgets as
the original schedule. It does not identify sourceCount(d,c,t) with the
companion count at original input t when c>t.

Then freeze the entire rank>=3 quantitative source statement over

    D(d,c,j,t)=Int(sourceCount(d,c,t))+j,
    X(d,c,j,t)=f^[toNat(D(d,c,j,t))](t), on D>0,

with the exact C_d/T_d constants, all signed j,k, arbitrary natural R,
both displayed strict separation inequalities, exact same-input/same-mass
signed-index order, and the effective common-tail equality criterion.
No lower-rank separation oracle may be a new premise. The cubic startup
class analysis and higher-rank growing-mass induction remain to be proved.

A concrete sufficient equality tail to target is

    P = max(T_d,
            C_d*(c+e+|j|+|k|+1),
            C_d*(2*c+2*|j|+1),
            C_d*(2*e+2*|k|+1)).

For original inputs t,u>=P, require

    X(d,c,j,t)=X(d,e,k,u) iff t=u and c=e and j=k.

Since f(v)>v, P pays the cross-pair and both self-pair regions at every
v>=P. The two self-pair bounds permit extending adjacent-input separation
to arbitrary unequal inputs. T_d and P have explicit finite arithmetic
recursions; their effectivity is a conclusion of the eventual full target.

Downstream effect: the intended uniform treatment of masses comparable to
f(t) is retained. Every use outside the companion domain must go through
the new principal-start calibration. Genuine prefix splitting, the adopted
counter theorem and fixed-tail residue algorithms remain as accepted.

## Option B: keep only the genuine-input uniform region

Keep the corrected kernel definition unchanged and ADD the explicit premise

    max(c,e)+d+1 <= t

to lem:uniform's displayed region. The exact target then uses the accepted
actual kernels and their bridge without an out-of-domain identification.
This would be a narrower SOURCE CORRECTION, not a proof of the printed
unqualified quantitative region. It must not be promoted under the current
printed body unless root explicitly changes that body and records the loss.
It can first be accepted as supporting work while the broad region stays
pending.

For fixed c,e,j,k,R the same eventual consequences survive, since their
effective tail can include these finite domain bounds. Dynamic masses in
the induction need separate attention: an individual child block has
retained mass a=c+d(k-1), and a+d=c+dk<=f(t) at its own entry >=f(t),
so its own degree-(d-1) domain is genuine. Applying a LOWER-RANK PAIR
comparison at the smaller of two different entry norms also requires the
OTHER mass to fit that smaller entry. The manuscript's estimates
"pair mass <= 5B, entry >= B" alone do not imply that condition. A proof
must pay it explicitly, possibly after consuming an extra block; this is
not assumed discharged by the individual domain calculation.

Downstream effect: fixed-parameter eventual word comparison may still use
the narrower result, but the source growing-mass induction and every
quantitative use must expose the extra pair-domain premises. It is not
enough to carry forward the old informal uniform argument unchanged.

## Exact-scope point to settle before target freeze

The source says the "depths are defined and at least f(t)"; its final proof
sentence explicitly establishes positive iteration depth and output at least
f(t). The next exact contract should state separately whether the bound is
on integer iteration depth D, numerical value X, or both. A conservative
strong target can require D>=f(t) as well as X>=f(t), rather than silently
reading the former as positivity. No such supplier is assumed available.

S4's preferred source-preserving route is Option A, with a checked direct
first-budget calibration before any domain extension is applied. It retains
the displayed quantitative region. Option B is useful supporting work if
the broad induction needs longer, but must remain visibly narrower.
