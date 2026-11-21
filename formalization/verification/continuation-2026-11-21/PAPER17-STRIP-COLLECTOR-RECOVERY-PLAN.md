# Pending exact same-rank collector reconstruction

Fresh source reconstruction only, no historical bytes/receipt reused. Separate
from FiniteStripRecovery.FullFold and from any full arithmetic decision theorem.

## Immutable semantic inputs

Keep `PreparedProjection.LowerOperand` and literal `LowerOperandCode` table;
positive name j+1 addresses original slot j. A separate designated zeroRank
states what raw coordinate name0 means. A finite required-name list supplies
exact live formula AND outer graph/domain names, not every stale table slot.
Fix raw rank x to a. All other ranks remain arbitrary natural values.

## Proposed raw computation

For each required name in original list order, check its address. Name0 yields
(0,a) only if zeroRank=x. Positive names use actual table get? at name-1 and
only slots whose rank=x contribute. Others retain their names/bytes unchanged.
A matched coordinate returns a. Matched ordinary/count slots call the checked
closedOrdinaryValueField/closedOrdinaryCountField at that SAME a and original
field/endpoint codes. No fallback numeric value for failed reads.

Raw operand shape validation must precede dispatch: coordinate requires zero
unused payload, ordinary allows canonical iterate tag0 with zero endpoint
payload or entry tag1, count requires entry tag1 and iterate exponent0.
Other outer/field tags are invalid; do not use closedOrdinaryValueField's
all-nonzero-tag-as-entry behavior as a decoder. Actual ordinal domain
normality/properness/affordability remains checked by existing field guards.
Identity intervals remain outside this thin proper-field collector.

Return Option(Option(List(name,value))): outer none is invalid read/address,
some none is genuine valid miss, some(some reads) is success. Preserve the
first encountered failure without scanning later calls. Thus a tail invalid
behind an earlier miss does not change that earlier miss to invalid. Record
that exact ordered status, not a stronger global all-calls classification.
When required names are Nodup, successful touched names are Nodup; repeated
operands in separate slots still share x,a and original data.

## Proof boundary

1. Exact all-raw recursive branch equations and Computable f-relative program.
2. Successful result is exactly ordered matching required names, with genuine
   original values/status at fixed a. No assumed totality of field evaluation.
3. For every raw valuation rho with Function.update rho x a, matched reads have
   same actual values; untouched ranks are unchanged. Source meaning only uses
   required support, never all-table PreparedTableTied/zRank restriction.
4. Feed successful reads to checked actual fold; prove dual slot-valuation
   agreement on every ORIGINAL live name, hence all-valuation hit-path iff.
   Specialize outer graph/domain formula independently of possibly negated test.

No proof that failure makes a branch false without a separately frozen required
call implication from the actual outer guard. No finite strip enumeration,
rank/dimension coverage, parity normalization, all-large projection or full QE.
