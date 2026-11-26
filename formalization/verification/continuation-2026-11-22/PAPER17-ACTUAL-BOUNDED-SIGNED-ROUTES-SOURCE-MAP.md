# Paper 17: source-static typed bounded signed-row candidate routes

Manuscript: [arithmetic proof](../../../17-permitted-control-canonical-comparison/sections/arithmetic.tex), lines 197–246.

The route tree is represented by a finite list of root-to-terminal traces with literal ordered positive comparison packets. Each zero step recurses on the exact typed source-static successor and consumes one unit of the supplied depth; malformed/nonzero syntax is not routed through a guessed zero successor. Nonzero or already-linear terminal candidates are emitted even at zero remaining depth. The exact static active test recognizes only a nonzero-weight highest nonlinear operand. Signed terminal tests are equality/order/positivity with either sign polarity, not nonlinear modulo.

Every path guard reads only that path's actual tied table at the same original control and same raw lower baseline, with one shared highest value. Linear terminal packets similarly require only their own actual tied lower table. No AND of all unchosen descendants' availability. This stage proves literal finite layout and local availability, not execution, true fuel adequacy, recursive dimension projection or raw effectivity.
