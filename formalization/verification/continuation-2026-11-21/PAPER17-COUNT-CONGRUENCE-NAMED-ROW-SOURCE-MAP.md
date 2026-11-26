# Original one-count shared residue to a named row: target freeze

**Printed source.** Paper 17, sections/controls.tex:172–183,
prop:entry-residues, gives the actual finite omega-tail / complementary
proper interval count and its exact sufficient tail. The continuation table
at controls.tex:206–216 distinguishes count modulus m from value modulus 2m.
Sections/arithmetic.tex:231–240 prescribe raw input modulo 2m, always
shared by all occurrences of that input, without any implicit half-field.
Here we retain one original general proper interval (lambda,mu) and the
actual signed atom m | c + u*x + v*tau(x), both terms using x=rho(rank).
Only m is positive; c,u,v are arbitrary Int, including zero and negatives.

**Executable syntax.** The output table is generated, never supplied:
the single original coordinate at positive name 1 with unchanged rank
(and exact literal coordinate/tag bytes). List.range (2*m) and a right
fold form an OR in the existing radix-six NormalForm. For each retained
j the one actual atom is (2*m) | slot_1-j, using modulus-minus-one 2*m-1.
The selection test is m | c+u*j+v*D(j), implemented by remainder of the
absolute value of the entire signed sum (not by natural subtraction).
D(j) is k for canonical positive short length k; otherwise it is
signed floor(j/2)-ceil(N(mu)/2). The original coordinate contribution is
j, including its odd bit, never 2*floor(j/2). A nonretained class is
omitted; the OR of zero classes is false, not an invalid or missed read.
The row uses only plain name 1, and the target proves coverage, positive
names and Nodup for the generated table, not as input hypotheses.

**Inputs and actual witnesses.** Retain the selected f with its B, one
proper original entry, positive m and the exact printed max
max(N(lambda), max(N(mu)+3,max(m,B))) at x=rho(rank). This pays both
entry affordability and the original control-residue threshold. The
existing short-gap recognition (#712) proves the canonical positive
classifier iff the actual proper endpoint equation and its zero branch
iff actual LongField. The original EntryStatementChecks.fixed_entryResidues
then supplies actual FirstEntry with count k or its signed residue; it
applies to the original general mu. Complete-count tables are not a
replacement with mu=0. The original closed domain and #728 actual
prepared tied read calibration give actual count/read at the same rho.
No FirstEntry success, count, preselected residue, output formula,
coverage, or field table is supplied. Row evaluation is tied only by
slot 1 = x, and the compiler uses j=x%2m without assuming a parity. The
numerical transport is x≡j mod m and floor(x/2)≡floor(j/2) mod m from
x=2m*q+j, and signed ModEq preserves the original weighted sum.

**Raw boundary.** The fixed raw builder and printed-tail compiler are
specified PR on all inputs. Raw modulus zero returns none. Positive
modulus malformed endpoint bytes have numeric output only: the target
claims neither a complete raw properness validator nor actual semantics
except on original canonical NONote inputs with proper shape. Literal
atom/OR calibration identifies the output with the existing encoded
signed row, not with an auxiliary Boolean-as-an-oracle.

**Not paid.** Not arbitrary mixed modular rows, all-rank table/name
collation, reserved-name-zero alias, optional halves, source-Boolean
guard insertion, outer call definedness, total strip selection/coverage,
a dimension loop, or the whole printed field comparison #704. #714
tails, #716 form code and #718 all-order comparison are separate order
normalization suppliers, not residue/affordability evidence for a
new synthetic row; in particular collation would have to derive the
actual selected lower H read/domain from the same guard and fixed raw
coordinate. #728 can consume a prepared plain row/tied table, but does
not make an arbitrary such table the source of this adapter.
