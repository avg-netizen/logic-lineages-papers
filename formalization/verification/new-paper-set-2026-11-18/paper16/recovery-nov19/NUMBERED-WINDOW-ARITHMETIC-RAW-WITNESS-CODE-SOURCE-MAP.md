# Actual supplied raw rule witness numeric codec

Supporting source scope for ordinals.tex lines 10–76; actual numeric
codes of the accepted literal raw witness data only. No full list
of raw/class path certificates, executable coded relation, object
arithmetic/representability, or ID_1 proof claimed here.

The literal numerical syntax codec (#450) and actual ordered tagged
fields are reused. The occurrence-list code maps each literal NTerm
to its actual Nat code, retaining exact list order and duplicate
occurrences. ReplacementWitness is one tagged node carrying the three
ordered kept/removed/added lists, not a multiset normalization or a
search; semantic witness validity remains the independent #453 bit.

The eight RawRootWitness alternatives are tagged separately. Mark
retains its full finite label, Select its exact Bool side (only code
0 or 1), actual ordered index, and entire ordered literal Ty domain
tuple; Stat retains the entire occurrence partition. Lower, Copy,
FAbs, Beta, and Bottom carry no extra hidden witness data. Their actual
raw step certificates still check the original independent rules in
#454. This codec alone does not certify any endpoints.

RawWitness uses a separate tagged root wrapper plus all five actual
recursive contexts: lambda, ordinary base, numbered base, numbered
extra, and auxiliary function only. All three ordered list context
indexes are encoded literally. The decoder rejects other tags and
field counts, malformed components, and cannot invent an auxiliary
argument step. Recursive children are actual strict tagged fields
below the parent's code. The exact comparator requires success
soundness at every fuel and total roundtrip at any fuel from the
actual code upward; the public decoder uses the input code as fuel.
Success/roundtrip/malformed rejection are of literal objects, not
just up to Primary.
