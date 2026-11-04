# LAST ROUND5: actual unary finite-DNF quantified decision

SourceSnyatkov2008Theorem1p42display(1)/p43Boolean normal-form matrices include
fixed integer combinations of f(v+k) and v. We prove a real total decision
procedure for its ONE-variable finite-DNF shifted-Phi+linear fragment, using
round4's actual unconditional tail-sign theorem, not a supplied solver. This
is not full arbitrary-Boolean-AST conversion, multi-variable quantifier
elimination, or a full source Snyatkov/arithmetic comparison theorem.

Atom=((original signed-Phi row,c,d),desired sign), clauses are finite lists,
matrix a finite list of clauses. ONE n is shared by EVERY atom, no entrywise
independence. Matrix is disjunction of conjunctions; empty matrix false and
empty clause true. Desired signs outside{-1,0,1} are accepted data but false
atoms, using the actual Int.sign. All coefficient cancellations retained.

The exact common source domain is the MAXIMUM of the original atom domain
bounds over ALL original occurrences, even zero/cancelled coefficients and
false clauses. Prove equivalence with genuine nonnegative n+signed-offset for
EVERY original occurrence. Threshold D+1+sum(atom thresholds) is an explicit
valid tail witness beyond every actual atom tail. Check every valid input below
that threshold with actual source evaluation; use actual computed matrix tail
for all remaining inputs. Existential and universal bits are BOTH concrete and
uniformly primitive recursive. No missing evaluator/growth/decision/class-field
premise introduced. No hidden claim for n below the original common domain.

Latest user limit: this is the FIFTH and LAST coherent restart-relative round.
After constructive exact-gate completion (or an honest scoped obstruction),
PAUSE/reap/save all immutable accepted/draft scope/evidence; NO sixth subject or
automatic restart/publication. Comparator preflight/freeze before proof.
