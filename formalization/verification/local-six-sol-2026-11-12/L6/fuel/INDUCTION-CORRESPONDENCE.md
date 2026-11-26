Latest status: full final source tuple checked by BUILD-081; see
CHECKED-CHECKPOINT.json and HANDOFF.md. The proof correspondence below
was written while the gates were pending, and is retained as that record.

# Fuel proof correspondence (candidate, pending exact gates)

The frozen targets remain Definitions.lean and Targets.lean, with their original
preflight hashes in FROZEN.json. This document maps the already authored proof
to those unchanged targets; it does not introduce another contract.

Write Q(i,s,n,f,a) for the literal source term equality
call(checkerTag,[i,s,n,f,a]) = 1. The original input order is retained at that
outer call. The wrapper's accumulator uses [s,i,n,f,a] only internally.

StepProof.openStep derives Q(i,s,n,f,a) -> Q(i,S(s),n,f,a) from actual registry
lookups and their ordinary defining equations. The previous accumulator value
is the first argument of leftOr. Its source equation leftOr(1,x)=1 needs no
property of x, so the nested opaque q0 call does not become an oracle premise.

InductionProof.openIncrement uses the actual full-language PA induction
constructor on the following Formula(ctx+1), where d is variable0 and all
five original runtime terms are renamed under its binder:

    Phi(d) := Q(i,s,n,f,a) -> Q(i,s+d,n,f,a).

The base is ordinary PA s+0=s and equality replacement for the literal Q term.
For the induction step, StepProof supplies persistence at s+d; PA
s+S(d)=S(s+d) transports its conclusion to the successor instance of Phi.
Both temporary local hypotheses are discharged before generalization.
Derivation.arithmetic(.induction Phi) then yields ALL d Phi(d). The d binder
is inside the object language. There is no external numeral/fuel/bound schema.

InductionProof.openMonotonicity opens that actual ALL derivation with a fresh
object variable d, uses equality replacement from s+d=t, and eliminates d by
the already derived ordinary existential-elimination rule. Its conclusion is

    (EX d, s+d=t) -> (Q(i,s,n,f,a) -> Q(i,t,n,f,a)).

The public source sentence closes six arbitrary runtime inputs: index, both
fuels, context, formula and certificate. The existential difference witness
stays inside its order guard. The final Proof module chooses q0, its literal
wrapper q, the retained-parameter CK program and the real producer before
actualRegistry chooses c/rho. It embeds these registry-equation PA proofs in
the SAME constructed source S and changes no applyProv/prD definition.

NativeProof is a separate chain. It first proves exact normalized bounded-OR
semantics on ALL raw index inputs without a Boolean premise on q0. It then
uses the original external certificateFuelMonotonicity theorem to recover
exact equality to the original numeric checker at EACH ordinary Code/fuel.
That calibration is used only to install the actual source tuple. It is not
used as an internal source derivation in the induction chain.

Compilation status: scaffold preflight BUILD-061 passed; first Native and
Logic drafts failed BUILD-064/065 and are preserved. Their released local
repairs and independent induction gate are queued. No fuel proof acceptance,
full HB2/HB3, certificate-history/quotation preservation or source collapse
is claimed here.
