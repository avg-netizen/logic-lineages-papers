# Independent factorial-control pre-scope review

Approved for proof authoring. All four freeze pins match. Current controls.tex
factorial definition, lem:control and orbit-potential match the proposed scope.
The separate definition does not mutate the frozen near-control definitions.

The natural implementation G(n)!+2*p(n)-2 is accompanied by a required exact
integer-cast equality at every n. This is essential: the printed signed
subtraction cannot be justified merely by natural truncated subtraction.
The obligation includes n=0,1. The complete factorial branch also retains
primitive recursiveness, evenness, majorization, the factorial upper estimate,
full double-tower adjacent growth, strict next-G bound and eventual fixed-level
bound. Explicit n>=101 F6 domination strengthens the printed eventual clause;
it must be proved and is not certified by scope review alone.

The potential law uses positive natural modulus m and n>=max(m,0), with signed
p(n)-1 retained in Int.ModEq. The separate orbit statement is unbounded in i,
including i=0, and uses the source B_f=0 threshold. No tail-only growth or
arbitrary chosen control supplier replaces the literal factorial function.

Native exact aliases, standard axiom closures and recursive evidence remain
required. Even if proved this packet covers only factorial laws and orbit;
near-control assembly and the full comparison proof are separate obligations.
No compiler run during this review.
