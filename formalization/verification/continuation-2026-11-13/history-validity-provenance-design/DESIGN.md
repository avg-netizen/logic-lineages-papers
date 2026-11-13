# Operational top-entry validity provenance: read-only design

No Lean targets or proofs authored, no compiler/Git run. Source review of HistoryKernel, HistoryRunSplice and HistoryLengthConservation; generic registry and SAME-source installation remain distinct.

## Necessary correction: nonzero, not equality to one

For arbitrary v, the valid conclusion is v(lineCode) != 0. HistoryRuleSuffix.conjunction a b = choose a 0 b. Therefore a=2 and b=1 produce1. HistoryKernel.acceptedTest compares the WHOLE lineDispatcher to1; it does not compare v to1. Concretely use v=constant2 and logical=constant1 at a rule0 line: the literal dispatcher returns1, the kernel appends its actual context/raw, yet v(line)=2. These arbitrary leaves need not satisfy NativeLeaves; the requested generic operational theorem has no such premise. This is a direct AST counterexample explanation, not a newly checked Lean counterexample.

Do not add Boolean range as an assumed shortcut. The fresh explicit validator can later PROVE internal range0-or1 from its literal equality-code output, hence turn nonzero into1. NativeLeaves calibration alone is not internal range.

## Exact proposed generic conclusion

Fix installed iterator of HistoryKernel.kernel v l a x, and actual pair/cons/decoder nodes. Starting from pair(1,lines), i.e. SOME empty history, an actual iterator result pair(succ(cons(pair(context,raw),tail)),remaining) implies internally:

  exists lineCode, left(lineCode)=context AND left(right(lineCode))=raw
                   AND call(validTag,[lineCode]) != 0.

All quantities are arbitrary internal Terms. The selectors must be actual installed HistoryDecoder copies, related by their proven copy coherence. No external Line witness, decoded-list premise, NativeLeaves calibration, or proof that v ignores rule/payload is supplied. The witness is the line actually read at the last nonstuttering successful step, not a newly synthesized line with changed rule/payload.

Prove this for arbitrary iteration count and remaining-lines output. Specializing count=lines and remaining=0 yields exactly the original full encoded-bound run. This stronger operational invariant avoids a new length installation requirement. Initial SOME empty is essential: from arbitrary initial history, an unchanged preexisting top has no guaranteed validity provenance. For arbitrary initial history the correct alternative would be inherited initial top OR a newly consumed witness.

## Internal induction route and exact suppliers

Use object-language induction on the actual iterator count, keeping the initial lines/index/fuel fixed and universally binding output context/raw/tail/remaining.

* Base: iterator0 is the initial state. Actual pair injectivity and cons nonzero exclude a nonempty output history from SOME empty.
* Successor: actual recurrence applies the literal kernel to the previous iterator value. Internally decompose that numeric state with HistoryIteratorSuffix.SurjectivityProof/ReconstructionProof and actual decoder inverse/copy laws, not native State codec totality. Split its remaining lines as0 or actual cons using the internal list reconstruction.
* Empty lines: HistoryRunSplice.IdleProof supplies exact kernel stutter. The prior iterate has the same successful nonempty output, so apply IH. This is why naive extraction from the final iteration alone is wrong: encoded-bound runs commonly finish with many stutters.
* Nonempty lines: split previous option0 versus successor history. NONE cannot become successful; use the literal nextOption zero branch. For SOME history, HistoryKernel.SuccessProof.successfulParts recovers actual dispatcher=1 and newHistory=output from successful transition. If necessary first recover the actual remaining-tail equality using NormalProof.kernelEquation and pair injectivity; successfulParts' explicit rest must match.
* HistoryKernel.EntryProof.entryEquation/someEquation identify newHistory as actual cons of pair(left(line),left(right(line))) and previous history. Cons successor injectivity and HistoryCancellation.InjectivityProof.pairInjective identify the requested context/raw from the final top. This yields the real consumed line witness directly; IH is not needed in this active success branch.
* Unfold actual lineDispatcher conjunction. Its zero-v branch is0, contradicting dispatcher=1. Hence v(line)!=0. No need to infer any leaf range or rule-specific payload shape.

HistoryLengthConservation.SomeStepProof already demonstrates the useful NONE/SOME case split through OptionProof.optionGraph and ConsRunProof.someCons; reuse these exact operational equations, not its arithmetic length conclusion as a validity oracle. RunSplice encoded-bound conversion and conservation are unnecessary for the minimal arbitrary-count invariant, though compatible with specialization to the full original run.

## Registry discipline

From iterator installation at itag, the actual kernel child is kt = itag + stepTag(iterationBase) + 1, as already used in HistoryLengthConservation.SomeStepProof and HistoryRunSplice.IdleProof.kernelInstalled. Recover dispatcher child dt = HistoryKernel.TransitionEquationsProof.dispatcherTag kt v l a x. Recover validTag through the actual first test child of lineDispatcher's select/conjunction and the function child of applyOne v lineCode; derive this with functionChild/argumentChild, never assume a standalone unrelated v node suffices. EntryProof supplies actual context/raw wrappers and nested decoder addresses; expose their installed copies or transport to designated decoder tags explicitly.

Generic target first quantifies registry p and exact installation equalities. It does not claim those helper nodes at a previously chosen SAME root. For an existing literal checker root, use HistoryMachine.SourceProof.iteratorInstalled, kernelInstalled and the actual nested-child extraction to instantiate; lift its theory derivation into S with the existing inSource monotonicity. This minimal design needs no new length Program installed, so it may be installable at the present literal root without changing its AST. A later explicit-validator source uses a fresh root and rederives addresses there.

## Consumer boundary

The conclusion supplies nonzero validity on the ACTUAL old line. It does not license replacing that line by mpLine/context/raw alone for arbitrary v. The fresh lineValidator must separately prove field-only invariance (literal context/raw selectors) and internal Boolean range; only then can recovered provenance give validFormula(context,raw)=1 and support the implication-conclusion scanner law. Neither this provenance invariant nor that future scanner law alone proves full HB or source constructor closure.
