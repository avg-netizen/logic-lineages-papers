# Internal numeric iteration for the original application-validity stack

This four-target supporting component supplies iteration algebra for the
concrete original application-validity stack toward paper 06, `lem:id1`.
It does not prove the stack worklist append/decomposition law, payload-based
termination, sufficient fuel, recursive validator calibration, or internal
application-validity closure. No numbered paper statement is promoted.

## Original syntax and arities

For an arbitrary actual unary `GorbowPRProgram.Program` AST `T`,
`InternalNumericIteration.repeatProgram T` is literally

    Program.recursion (Program.projection (0 : Fin 1))
      (Program.composition T
        (fun _ : Fin 1 => Program.projection (1 : Fin 3)))

The result has arity two, with inputs `[count, initial]`. The base has arity
one and returns `initial`. The step has arity three and receives
`[predecessor, recursive result, initial]`, as fixed by the original
`GorbowPRProgram.evaluate` recursion clause and the original arithmetic
graph's recursion equations. Thus projection 1 selects the recursive
result, not the count and not the initial-state parameter. The latter two
are ignored by the step. No new primitive or representation witness is used.

Expanding `repeatProgram` and `repeatStep` at
`T = InternalApplicationValidityStack.transition node leaf` gives exactly
the existing frozen `InternalApplicationValidityStack.iterate node leaf`
AST. The stack definition is not edited or redefined. This source-level
identity is pinned below; native elaboration is still pending. The generic
definitions do not import the stack implementation, so there is no circular
consumer/supplier dependency.

This is ordinary NUMERIC recursion. It is not
`InternalRawListRepeat.repeatProgram`, which uses the original raw-list
recursor. The already checked raw-list commutation argument is a proof
pattern, not a replacement for this numeric target.

## Exact four frozen target meanings

Write `R(out,k,s)` for the literal original `programGraph` of
`repeatProgram T` at output `out` and inputs `[k,s]`. All four statements
quantify arbitrary positive operator bodies, actual unary PR ASTs, variable
types, and symbolic original arithmetic terms. Their conclusions are
`Nonempty (InternalCalculus.Derivation body [] ...)`, with the original
object-language equality and biconditional. There are no semantic truth,
accepted-program, standard-numeral, canonical-encoding or well-formed-state
premises.

1. Zero: `R(out,0,s)` iff `out = s`.
2. Front successor: given the actual graph `T(next,s)`,
   `R(out,succ k,s)` iff `R(out,k,next)`.
3. Addition fusion: given `R(mid,m,s)`,
   `R(out,OrdinaryArithmetic.addTerm m n,s)` iff `R(out,n,mid)`.
   The order is first `m`, then `n`, with the same arbitrary final output.
4. Fixed point: given the actual graph `T(f,f)`,
   `R(out,k,f)` iff `out = f` for every arbitrary symbolic `k`.

The transition and intermediate graphs are hypotheses INSIDE the internal
formulas. They are not external assumptions granting an interpretation of a
program. The full-output biconditionals cannot be replaced by one-direction
acceptance, bounded standard-model calculations, or an exposed semantic
closure premise.

## Permitted proof route, not an additional target assumption

The inherited internal primitive-recursion zero/successor introductions,
program totality/functionality, graph composition and equality transport
supply the primitive numeric step. A four-state universally quantified
commutation invariant can follow the checked raw-list pattern, with the
original full-language natural-number induction schema replacing list-code
induction. This yields front successor internally at arbitrary counts.

Addition fusion may use natural induction in the second count and the
original arithmetic `additionZero` and `additionSuccessor` laws, preserving
the actual `addTerm first second`. Fixed-point stability uses the same full
internal induction and functionality. Neither route permits standard-model
truth-to-derivability reflection. Existing original induction is a rule of
the unchanged calculus, not a newly assumed theorem or class field.

## Source and validation boundaries

The original paper application rule and quotient-arithmetic material remain
at paper 06 lines 537-556. This packet is a supporting program-calculus
component only, not a direct assertion that those source rules are proved.

`FROZEN-SPECIFICATION.json` pins these three specification files, this
correspondence, and the original AST/calculus/graph/commutation suppliers.
Only these NEW component files have been written. Existing frozen targets,
proofs, arithmetic syntax, stack syntax, register, build policy and Git state
are not edited by this worker.

Independent specification review and bounded native preflight must pass
before mathematical proof authorship. Neither has run at this freeze.
No compiler is owned by this worker. Subsequent checks must use only
`scripts/check.py` with the existing serialized 2048 MiB heap / 1536 MiB RSS /
2048 MiB minimum-free / one-thread profile, under a fresh sole-slot grant.
No full-root, native acceptance, remote-CI or publication claim is made.
