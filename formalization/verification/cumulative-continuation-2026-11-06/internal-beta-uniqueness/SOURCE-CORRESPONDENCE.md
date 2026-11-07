# Original beta functionality

The frozen target literally embeds two instances of the original
OrdinaryArithmetic.betaFormula with identical a,b,i parameters and arbitrary
remainder terms r,s, concluding embedded original equality r=s.
It imposes no additional restriction on code, index, body or variable type.

Each beta block retains quotient q at bound index 0 and strict-bound witness
d at bound index 1. The proof transports both original quotient equations
and remainder-bound equations through fresh-variable maps, without changing
shared parameters or their identities.

For q<q', the original witness q+succ(w)=q' expands the second product by
internal multiplication distributivity and left-successor. The first bound
r+succ(d)=M then forces (q*M+r)+succ(k)=q*M+r, contradicting an internal PA
derivation. The reverse case uses the second bound. Equal quotients reduce
directly to existing left-addition cancellation. No semantic Nat theorem,
replacement beta relation or admitted arithmetic fact is used.
