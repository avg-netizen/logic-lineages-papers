# Literal arithmetic halting conjunction

Paper09 hardness.tex lines295–307 uses the odd constant C=2b+5 and precisely the three equations z+4=2^e(2t+C), y=F_S(z), y=w+w+1, with F_S(z)=Gamma_b(z+4). This component treats that displayed arithmetic system over natural variables t,z,y,w, using the already proved actual blank-table transition-clock Gamma.

EffectiveArguments proves primitive-recursive coefficient 2^e, odd constant and argument, plus n≥5, n>b, n≥t and v2(n)=e for n=2^e(2t+C). No variable exponentiation source primitive is introduced: the exponent is the fixed input index e.

ExactFixedWitness proves, for each t, existence of the original z,y,w witnesses iff H(e,n)=true. It also verifies the explicit source witnesses z=n-4, y=Gamma_b(n), w=(Gamma_b(n)-1)/2 when H succeeds; subtraction safety is proved, not assumed.

ExactHaltingReduction proves the entire existential conjunction satisfiable iff the actual blank-table program e halts, for every fixed b. Eventual halting supplies a sufficiently large t using n≥t and the exact monotone transition-clock test. The reverse direction uses the actual halting equivalence, not an oracle.

The equality y=Gamma_b(z+4) is an arithmetic graph here. A Gamma-parametric actual source S graph, addition/constant gadgets, flattening, collision/eraser aggregation, strict/weak comparison reduction, Pi01 membership and O(e+log(b+2)) gate count remain separate obligations. No full hardness or whole-source promotion is claimed. Enumeration is the explicit accepted finite-table model, not an inferred manuscript-specific syntax.
