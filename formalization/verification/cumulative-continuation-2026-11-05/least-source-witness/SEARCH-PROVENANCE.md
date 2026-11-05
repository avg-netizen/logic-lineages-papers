# Concrete total search and leastness

The implemented predicate is `!need || actualBodyAnswer(updatedCurrentTable,n)`.
Here `need` is the actual checked source decision on the literal existential
parent. If it is false, predicate zero is true. If it is true, source truth,
instantiated-body admission and literal update calibration supply a true
candidate. The actual Nat.rfind program therefore has a domain proof for every
raw input, not a premise restricted to a supplied witness.

Part.getOrElse 0 is the fixed result specification. Global termination proves
that its value belongs to the concrete search. Part.eq_some_iff then identifies
that search with the exact total result; Partrec.rfind supplies the actual
program, proving Computable for the fixed result. The default is never used.
The witness option is selected by the same actual parent decision.

Nat.mem_rfind provides both a true candidate and false answers for every smaller
natural. Literal code calibration converts those into actual source truth and
minimality at original-name updates. The accepted domain is unchanged, including
its existing nonlinear restrictions; unsupported input returns none.
