# Actual counter-leader strict bounds

Source08 paper.tex lines 452–457 and 470–482 assert H/2<E^r_c(t)<3H/4 on an effective tail, for the literal descending entries and leader H=Phi(u). This component reuses the accepted exact CounterLeaderExpansion definitions and identity, with r=n+3.

The sufficient tail is explicitly strengthened to max(c+2r+1,2c+10). The first part of ActualResidualBounds is unconditional for the totalized actual kernel definitions: each count L contributes at most its actual norm increase Phi^[L](seed)-seed, so the complete descending residual list satisfies t+sum≤u. On the displayed strengthened tail, the cubic residual alone exceeds ceil(c/2), using the existing actual unsigned cubic cut and quadratic count. No generic count oracle or supplied positivity premise is introduced.

The second target is the exact strict source bound, expressed as H<2E and 4E<3H, avoiding rational rounding. Existing literal control growth gives 4u<Phi(u); the accepted integer identity and actual leader parity then suffice. The stronger telescoping estimate replaces the paper's looser rankwise upper estimate without changing its conclusion.

The tail is sufficient and effective, not claimed minimal and not silently identified with the preceding identity-only tail. Equal-leader recognition, rank collision, whole lem:counter, whole uniform separation and numerical compiler obligations remain separate. No unsafe signed recurrence is used. Accepted supplier files and standard caps remain unchanged.
