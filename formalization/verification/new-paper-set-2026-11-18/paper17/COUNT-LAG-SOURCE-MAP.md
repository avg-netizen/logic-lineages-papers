# Actual event-count lag: supporting scope

Source entries.tex paragraph after lem:propagation: strict persistence gives
upper stop ≥lower stop+k+1, weak persistence gives ≥lower stop+k. This is a
supporting conditional budget lemma, NOT full lem:gap-input.

CountLag operates on genuine FirstEntry trajectories for two actual selected
controls (allowing different selected f,g is harmless strengthening), each with
source proper limits/limit-or-zero targets and affordable tail max(2,Nlambda,Nmu).
Both actual profile bounds ≤S are retained. tau/sigma are certified by actual
FirstEntry, not arbitrary counters. Neither upper survival at k nor survival
later is assumed. Initial dominance of actual positive relative limit of a proper
lower interval must force k<sigma; later survival is proved in the induction.

Strict case assumes actual initial strict relative-limit dominance and next upper
budget g^[i+k+1](u)≥f^[i](t)+S for each i<tau. Conclusion tau+k<sigma.
Weak case assumes initial weak dominance and compares next upper with next lower
f^[i+1](t)+S; conclusion tau+k≤sigma. Equality/strict split must use correct source
propagation rules; lower noncontraction justifies strict alternative.

The per-step budget conditions are explicit supporting hypotheses only.
Full source gap/input must derive them from actual selected control growth and
reserve norm estimates, with effective tails. No source numbered promotion here.
No ordinal norm monotonicity, relative-step oracle, survival or count bound premise.
