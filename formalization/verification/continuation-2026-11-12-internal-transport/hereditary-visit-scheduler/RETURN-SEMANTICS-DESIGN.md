# Next semantic contract: standalone return algebra

Proposal only. The checked scheduler does not yet implement this algebra.

## Missing annotations

A job currently contains raw code, original window c, and Gamma. It carries no
outer result type and no term-versus-argument-list role. A valid recursive
observer needs both. A future semantic job should distinguish:

* `Term(tau,raw,c,Gamma)`;
* `Arguments(raw,c,Gamma)`.

The forgetful projection drops role/tau and must commute with the checked raw
expansion. Lambda term children receive the codomain and extended Gamma;
application children receive arrow(domain,result) and domain; ordinary BASE
and numbered BASE/extras become Arguments jobs; argument cons schedules one
Term at its stored type and one Arguments tail. Deletions preserve the role
and term result type. No typing can be inferred merely from a raw frame tag.

## Smallest standalone return Programs

Propose `returnRoot : Program 3`, with inputs original packed root and two
completed child-slot results. It has no recursive call and no Q parameter.
The original root metadata determine the branch:

* variable/bottom: same literal metadata as rootObservation;
* lambda: pair the child scalar with original codomain, retaining domain;
* application: typed first scalar at arrow(domain,result), typed second at domain;
* ordinary: sort the completed typed BASE list, retaining head class/result;
* numbered: sort BASE only, retaining ordered extras and label/head class.

Separately `returnArgumentsCons : Program 3` takes original raw cons node,
completed head scalar and completed tail-list value and returns the literal
list cons of pair(stored type,head scalar) and tail list. Nil returns zero.

Freeze an exact native substitution theorem: supplying actual Q evaluations
for term children and actual encoded argumentValues Q for list children yields
exactly the existing rootObservation Q result on every original typed term.
The list theorem yields the actual encoded argumentValues on typed nil/cons.
These are executable arithmetic return constructors, not hypotheses that an
unknown recursive observer already supplies the desired parent result.

Native laws and subsequent internal graph composition laws remain separate.
No source closure or representative calibration is needed merely for these
return-algebra equations; semantic uniformity remains a different obligation.

## Composition still missing

To form a complete layer return, pair fixed rootObservation R with the newly
assembled recursive-child root and the ordered deletion-result row. Do not
substitute the whole evaluator as a literal Program Q in its own definition.
The machine must obtain child and deletion results through its work stack.

Argument-list worktree nodes also have deletion successors, whereas their
root assembly needs only the head/tail argument-row results. Either prove that
such deletion results are computed and discarded under the over-enumerating
schedule, or prove a pruning simulation before omitting those jobs. Their
presence cannot be silently identified with semantic typed-child observations.
BASE result ordering is canonicalized only at the owning term return; argument
list traversal itself preserves order and multiplicity, including extras.

No return transition, recursive evaluator, fuel/administrative count, primitive
cost theorem, internal uniformity, or final class-coherence integration is
asserted by this proposed standalone packet.
