# Actual evaluation at the fixed all-zero valuation

The explicit projection evaluates every original weighted summand via the already
proved actual `valueAt`/`itemValue` algorithms at zero and keeps each atom's kind,
modulus and original Boolean position. Its output is a literal constant matrix,
so the checked constant evaluator produces the truth value at that fixed
valuation. HyperPhi evaluation here uses the already established finite iterator;
this is ground evaluation, not hyperPhi quantifier elimination.

Exact row, atom and radix-six formula calibration and primitive recursiveness
are required for the actual programs. This supplies the ground evaluator needed
to turn the all-witness one-name fragment into a closed decision procedure.
No oracle, arbitrary supplied evaluator or additional semantic premise is used.
