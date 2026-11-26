# Propagation next scope plan

Target full lem:propagation for actual profiles s_mu,s_nu, not arbitrary supplied
step or cost oracles. Use proved relativeMaximum and actual limit parts of
relative states u,v. Prefix norms ≤S instantiate the source uniform profile bound.
Require absolute states mu+u and nu+v below epsilon0 and lower next affordability;
strict budget condition derives upper affordability. Processes are still running:
the lower limit part rho=lim(u) is positive; in equal-limit cases both share it.

Strict branch: lim(v)>rho=lim(u)>0, N(u)≤b, upper next b'≥b+S, lower next
budget c≥N(mu). Show lim(R(nu,lim(v),b'))≥rho>lim(R(mu,rho,c)). Candidate rho
is affordable since N(rho)≤N(u) and actual profile bounded by N(nu)≤S.
Projection of upper R≥rho to its limit part uses actual limitness of rho.

Weak branch: lim(v)=rho=lim(u)>0, b'≥c+S, c≥N(mu). Lower R itself is an upper
candidate, since its norm≤c and upper profile≤S. Show upper next limit≥lower next.
This uses lower NEXT c, unlike the strict branch's CURRENT b.

Equal-budget profile branch: common positive rho and common next c affordable
for both prefixes; all eligible x<rho have cost_nu(x)≤cost_mu(x). Candidate
inclusion yields upper next limit≥lower next. This is a literal ordering of
proved actual profiles, not a replacement for deriving later equal-gap results.

This single-step lemma does not by itself prove count lag, gap/input comparison,
thick-block separation, eventual equality thresholds or arithmetic elimination.
Exact targets/source-map/freeze and independent pre-scope will precede proof.
