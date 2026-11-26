# Genuine successful-call free-substitution covariance

Use the existing actual locally nameless operations, without changing the
original-variable blocking or original-head branching. A typed free substitution
is a function θ : Ty -> Nat -> Expr whose image θ σ x is typed σ in one
outside bound context Γ. Images may contain outer bound indices. Thus capture
avoidance must lift each image by the actual binder depth; closed-image-only
substitution is not the endpoint.

Define freeSub θ d structurally: a free typed name becomes shift d 0 (θ σ x),
a bound index stays literally unchanged, a lambda recurses at d+1, and original
head declarations/base/extras/output annotations are preserved. Args are mapped
pointwise. Values inserted by θ are not recursively substituted again.

Required algebra, with actual values and arbitrary raw terms, not helper
compatibility premises supplied by the caller:

1. Shift insertion interaction, including arbitrary inner cutoff c:
   substitute vs (k+c) (shift (k+vs.length) c t) = shift k c t.
   This cancels the removed binder block after an image was lifted past it.
2. Free-substitution/shift interaction:
   freeSub θ (k+d) (shift k d t) = shift k d (freeSub θ d t).
   This requires the genuine shift insertion algebra under residual lambdas.
3. Full finite simultaneous-substitution composition:
   freeSub θ d (substitute vs d q) =
     substitute (freeSubArgs θ 0 vs) d (freeSub θ (d+vs.length) q).
   All free, retained-bound, replaced-bound and external-bound cases are
   included, with mutual Args statement. No empty-list simplification is
   substituted for this result.

Typed image preservation gives freeSub annotation preservation on typed inputs
and actual argument annotation equality. For call covariance, strengthen the
applyAux invariant to q typed under the consumed value-type prefix, values
BaseTyped in Γ, args CallTyped in Γ, and successful original call. Substitute
q at depth values.length, but values/args/result at depth zero. A lambda
increments both accumulated values length and substitution depth; the
empty-argument branch invokes composition. Original ordinary/marked residual
heads map old base/extras and append all remaining mapped args once. A free or
bound residual head cannot satisfy the success premise, even if θ would turn
a free variable into a head. Therefore do not claim unconditional Option.map
commutation of failed calls.

Final endpoint: source Typed Γ q σ, typed outside θ, CallTyped Γ σ args τ,
and apply q args = some r imply
apply (freeSub θ 0 q) (freeSubArgs θ 0 args) = some (freeSub θ 0 r).
No caller-provided output validity, head-shape preservation, covariance,
closedness or arbitrary variable-image compatibility assumption. Ordinary
images can later specialize this stronger auxiliary theorem. This is not an
alpha/name correspondence or an ordering/substitution-stability theorem.

Source: ordering.tex Definition original-spine application and its following
successful-call substitution paragraph; structural-stability proof uses that
identity. Preserve current checked definitions and freeze new endpoint/source
pins before proof. Review exact declarations separately before proof.
