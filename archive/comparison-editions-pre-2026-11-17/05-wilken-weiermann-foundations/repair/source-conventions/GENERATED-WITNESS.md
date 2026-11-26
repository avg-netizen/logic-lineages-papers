# A closed original source distinguishes two sum conventions

Write `Add(u,v)` for a literal binary natural-sum node and `Psi(f,g)` for
the primitive source node interpreted as ψ(ω ⊗ f ⊕ g). Its two immediate
subterms are f and g. In particular it is not parsed as a general product
and an extra sum outside that primitive node. Finite multiplication below
denotes repeated natural sum, not a primitive replacement of its AST.

Consider two macro-expansion policies L and R. Both use the same left-comb
expansion for every repetition, every other finite sum, every vector sum,
and the same binary box tail. They differ only in the three-operand sum
appearing in the active-sum partial clause:

    L: Sum3(a,b,1) = Add(Add(a,b),1)
    R: Sum3(a,b,1) = Add(a,Add(b,1)).

The analogous three-operand expression in an exponential partial may be
fixed identically in both policies; it is not used in this example.
Whole-free inputs are tested before these clauses. The distinction is not
an ordinal arithmetic distinction: each displayed Sum3 has the same value.

The closed, original-T term is

    A = λz:o. λx:o. ((λw:o. z) x) : o → o → o.

It has no recursor, no annotated recursor and no free name. Its source
syntax is used literally, without beta normalization. All function types
in this example have level one.

## The innermost abstraction and application

The assignment of `λw:o.z` is the vector `(f(z),1)`, where

    f(z) = Add(Add(Add(z,1),Add(z,1)),z).

Indeed the body vector has only coordinate zero, its w-size is one, the
normalizing multiplier is two, and the w-partial is `(z+1,1)`.
All operations here are binary or two-fold repeats, so L and R coincide.
Its value is `2(z+1)+z`, and its literal z-size is 9.

The body of the x-abstraction has scalar assignment

    g = Psi(1,Add(f(z),x)).

The box has argument level zero. Its otherwise displayed `+ n` is absent
when n=0, rather than an actual `+0` node. The x-size of g is
`1+(1+1+1)+1=5`, so the multiplier for this abstraction is 10.
Put

    u = Add(f(z),1),
    T_L = Add(Add(u,1),1),
    T_R = Add(u,Add(1,1)),
    K_L = Psi(1,T_L),   K_R = Psi(1,T_R),
    B = Psi(1,u).

The assignment h of `λx:o. ((λw:o.z) x)` has

    h_0 = Add(Repeat10(K),B),
    h_1 = Add(Add(1,1),Sum3(1,1,1)).

The repeat is the same left comb in both policies. The actual value of
h_1 is 5 in both. Its two possible trees are wholly z-free; their internal
associations therefore have no effect on the subsequent z-size or the
diagonal whole-free partial. The formulas for h follow directly from
Definition 2.18: the positive output of the scalar collapse partial adds
the positive head partial, of value 2, to the positive tail partial, of
value 3. There is no missing-coordinate `+0` node in h_1.

## Sizes at the outer abstraction

The literal z-sizes are

| expression | L | R |
|---|---:|---:|
| f | 9 | 9 |
| u | 11 | 11 |
| T | 15 | 13 |
| K | 17 | 15 |
| Repeat10(K) | 179 | 159 |
| B | 13 | 13 |
| h_0 | 193 | 173 |
| h_1 | 1 | 1 |

For example the terminal `(1+1)` in T_R is wholly z-free and has size
one. In T_L both additions above u are active. This is the entire source
of the difference. The outer multipliers are consequently

    S_z(h)_L = 2(193+1) = 388,
    S_z(h)_R = 2(173+1) = 348.

## A finite positive-coordinate separation

For these scalar expressions the value of positive output 1 of their
z-partial equals their z-size. This assertion is verified at each node:
the tracked leaf gives one; a wholly free scalar subtree gives one;
active sums add the two outputs and one; and the collapse head is the
constant one, whose grade-one diagonal partial has value two. Therefore

    (partial_0^z h_0)_1 = 193  (L),  173  (R).

Alternatively these numbers can be derived without the size observation:
the positive partials of f, u, T, K, Repeat10(K), B and h_0 have exactly
the successive values in the table.
Since h_1 is wholly z-free of value five,

    (partial_1^z h_1)_1 = 6.

The outer abstraction therefore has actual positive coordinate

    [[A]]_1,L = 193 + 6 + 5 = 204,
    [[A]]_1,R = 173 + 6 + 5 = 184.

These are finite ordinal values, not merely distinct ASTs or sizes. The
counterexample requires no evaluation of the enormous numerical control
or collapse. It refutes policy independence of the generated assignment
even in the closed, recursor-free, level-one fragment.

## The scalar values also differ

For completeness write H(t)=ψ(ω+t). Direct scalar partial calculation
gives `partial_0^z f = 11`, `partial_0^z u = 14`, and

    partial_0^z T_L = 20,   partial_0^z T_R = 18,
    partial_0^z K_L = H(20), partial_0^z K_R = H(18),
    partial_0^z B = H(14).

All ten repeated copies are z-active. Each internal sum contributes one
to the scalar partial, regardless of their common repeat association.
The common retained value after z:=1 is `10H(8)+H(6)`. Thus

    [[A]]_0,L = 388(10H(20)+H(14)+10) + 10H(8)+H(6),
    [[A]]_0,R = 348(10H(18)+H(14)+10) + 10H(8)+H(6).

Proposition 2.3(1), ψ(β)+k≤ψ(β+k), implies H(20)>H(18).
All factors are positive natural numbers, so the L scalar is strictly
larger. No global monotonicity of ψ has been used.

This does not refute termination. It shows why a zero-history comparison
problem must name its binary macro convention, and why the printed source
does not by itself single out one convention-independent function.
