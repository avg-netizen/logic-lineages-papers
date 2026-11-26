# Materially narrower decomposition interface, not another unchanged retry

Generic-only resource stop1794992706606710686-2 preserved at1,574,268KiB.
The split alone was insufficient. No initial/combined native attempt authorized.

Inspection found TWO genuine unused import branches in the generic proof:
1. TranslatedRationalProof imports SimplePoleLaurentProof and its reconstruction
   machinery solely for its third theorem. Generic Laurent law uses only its
   second theorem, the basic fraction-field lift equation on polynomials.
   That equation is directly IsFractionRing.lift_algebraMap with the already
   checked translated polynomial injection. Prove it locally from the definition,
   without importing TranslatedRationalProof or SimplePoleLaurentProof. Actual
   initial-residue supplier still requires reconstruction and keeps its proof.
2. BasicRationalProof imports polynomial Degree.Domain, CharP.Two, FieldSimp,
   Ring and proves rational uniqueness/characterization although generic Laurent
   proof only needs square decomposition. Create a single actual decomposition
   contract/proof module using BasicPolynomialProof and real fraction algebra,
   not uniqueness, no FieldSimp/Ring/CharTwo imports. Algebraically:
   (Eeven/Eden)^2 + X*(Eodd/Eden)^2
     = (Eeven^2 + X*Eodd^2)/Eden^2
     = (Enum*Eden)/Eden^2 = Enum/Eden = f.
   Use div_pow, mul_div_assoc, add_div, pow_two, cancellation and actual existing
   polynomial square decomposition. No oracle or replacement rational function.

Freeze exact new single decomposition contract identical to accepted Basic
ActualRationalSquareRootDecomposition in a distinct namespace. Independent
review before proof. Check this narrow supplier alone under parent grant.
Then generic proof imports it instead of BasicRationalProof and proves the lift
polynomial equation locally, while keeping genuine HahnSquareProof. Original
15pin split/13pin combined targets and full14pin period comparator remain
unchanged. No legacy file changes, cap increases or reduction of quantifiers.

Module splitting by itself does NOT hide transitive imports; the benefit here
is actually eliminating two unneeded proof/import branches. If fresh narrowed
proof still exceeds cap, stop this route and report hard environment blocker,
then choose independent current20 source work. No resource-failure retry loop.
Initial and combined proof feasibility remains separate even if generic passes.
