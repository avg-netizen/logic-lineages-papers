# Revised dependency order: actual marked builder before syntax interpretation

The uncompiled, unfrozen direct-M interpreter draft is preserved as REJECTED in rejected-designs/direct-m-interpreter/ProtectedSpineInterpreter.lean.txt. It must not enter any source gate. The finite environment helper draft remains unfrozen, for reuse only after exact review. No accepted/frozen file changes.

## A nonrecursive actual marked-value builder

Input: existing E, signature S, actual head inventory, retained previous family M, and literal valid parameter (f,tau,Gamma,base,extras). Output: an existing semantic Value, NOT decode(M(parameter)). At a descendant Delta first restrict the positional base tuple and weaken the entire extra down-set. All tests below then use these actual Delta inputs and previous M. No test recursively invokes the new builder or syntax interpreter.

Select: enumerate every positional base value and every tagged extra; for selected type rho enumerate the literal suffix decompositions rho=ArrowPrefix(domains,tau), INCLUDING the empty suffix separately. Build the whole tuple of previous-M values of the SAME owner retyped at each domain. For empty domains inspect the selected value's weak target bit directly; for nonempty domains inspect its ONE full application result at the target bit. Reject ill-typed raw branches, and prove valid-case tuple/output success from source inventory and the accepted full-action/marked-action contracts. No unary fold.

Copy: for target ordinary head g, test actual strict signature precedence f>g and every previous-M whole-owner weak bit against each positional target argument at its actual type. Stat: test actual head equivalence and a finite positional multiset witness between base values and target arguments, with weak matched and strict covering premises, plus the same whole-owner tests. Enumeration must retain source/target removal positions, nonempty removed set, and coverage of every added occurrence; no set-equality proxy.

FAbs: for actual lambda target at Delta use the approved coordinate-local least unused slot, restrict base/extras to Delta+, insert the literal port code into the down-set, and read previous M's weak bit at the actual opened target body. No self-recursive/new-family call. Spare slot, type-in-K, insertion validity and successful output are derived, not caller promises.

Set availability=true. Both weak and strict fields are the OR of these four positive tests. Every nonempty full tuple coordinate appends ALL arguments simultaneously to the weakened extras and consults previous M at the actual residual type. The builder's tuple behavior is definitionally the original head helper behavior; arbitrary M's own table at the unextended owner need not agree and is never assumed to agree.

## Builder proof dependency and encoding

This finite builder is definable before syntax interpretation: tests use only target Expr/Args inspection, finite occurrence witnesses, literal port construction, previous-M output lookups, and existing decoded table actions. Prove actual Value validity (typed outputs, tuple monotonicity, tuple naturality), monotonicity in inputs/M, and family (C) by comparing the same descendant coordinate and the same canonical fresh port. Weak/strict test positivity uses only previous data. Empty suffix and failed raw branches remain explicit.

Only after validity is established may syntax interpretation encode the builder to an actual hereditary code. The raw builder definition itself does not hide valid-case fallback. At family level, prove all parameters produce coherent monotone outputs before the actual family encode, as already required by the operator lemma.

## Syntax/helper recursion after builder

Keep actual mutual Expr/Args/nonempty original-spine recursion and call-local protected prefix. Marked nodes use the constructed builder on their recursively interpreted bases/extras. Ordinary-head weak fields are literal Fun OR this constructed marked counterpart; strict fields are its weak fields. Their full tables append all arguments and read previous M. Lambda fields use coordinate-local openings; lambda tuple fields scan the original body with the current consumed prefix, resetting when the tuple ends. Assigned free/ambient-bound values use their actual complete tables; consumed original-bound heads block with remaining arguments.

Now an assigned concrete marked image's full table is, by construction, previous-M lookup after append, exactly what the direct original helper computes. No same-M action-consistency law, fixedpoint premise, permutation-equivariance premise or staged associativity is added.

The dependency graph is acyclic: finite marked builder -> actual source/helper structural recursion -> structural validity/monotonicity/weakening/substitution/concrete correspondence; finite builder laws -> encoded actual operator -> monotone endomap/iteration. Some shared builder/source invariants can be packaged jointly, but every source/helper recursive cross-call must still strictly decrease original Expr/Args size, and no definition may recurse via a replacement syntax image or new family iterate.

Request independent revised conceptual dependency/recursion approval before exact definitions and target freeze. Full printed source obligations, finite fresh-witness adequacy and stabilization remain unpaid.
