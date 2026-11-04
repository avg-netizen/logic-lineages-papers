# Explicit logarithmic pre-aggregation DAG bounds

Paper09 hardness.tex lines 313–314 states that the arithmetic DAG uses O(e+log(b+2)) gates and explicitly says e is the numerical index, not its binary length. This component specializes the previously proved SourceMachineConjunctionPlan.ExactCompiledBounds to a direct logarithm of b+2.

The unchanged literal constant C=2*b+5 has bits b=Nat.log2 C+1. BitsBound states bits b≤Nat.log2(b+2)+3, including b=0. Substituting this into the accepted actual compilation bounds gives nodes≤80*(e+4*log2(b+2)+39)+4, equation-pair count≤10*(e+4*log2(b+2)+39)+1, and final context length≤10*e+40*log2(b+2)+392.

Result.nodes is exactly the sum of both source Input.specs lengths over the compiled forest, not merely the syntactic Plan.vertices accounting upper bound. The forest uses shared ground coordinates for the arithmetic intermediates, actual source S, all three binary constants, local-one allocations and primitive witnesses. The metrics are pre-collision/pre-aggregation source-forest vertices, equations and coordinates. They quantitatively support the paper's arithmetic DAG discussion without identifying that discussion with a final unfolded source tree.

No bound is asserted for final detector/aggregate expanded syntax, scalar encoded Nat magnitude or bit length, compilation/evaluation runtime, or polynomial dependence on binary length of e. No asymptotic API or stronger size metric is silently substituted. Historical sources, manuscript and registry remain unchanged; no export.
