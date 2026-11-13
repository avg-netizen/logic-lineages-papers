# HistoryLookup scope audit

Full exact6 gate: 1794566262907984480-31. NativeHistoryLookup separately passed
1794566065485527272-21; cross-tag destructor exact2 separately passed
1794566095993876863-5. Coordinator owns evidence verification and publication.

- Native endpoint uses the original GorbowProofChecker.History = List (Nat × List Nat)
  and Encodable.encode (history[index]?). It retains Option none = 0 and
  some entry = succ(entry encoding), so a legitimate zero-coded entry is not
  conflated with reference failure.
- The Programs are literal syntax: head/tail compose predecessor with the checked
  decoder, drop is a recursion applying actual tail, reference selects NONE or
  SOME(head), lookup composes reference with drop.
- InternalHeadCons/InternalTailCons permit arbitrary distinct installed destructor
  and cons addresses. Cross-tag pair agreement is proved internally from actual
  sector equations; the decoder inverse is not assumed across tags.
- InternalLookupZeroCons returns succ a, not a. InternalLookupSuccessorCons preserves
  the same installed lookup and shifts to the actual cons tail. InternalLookupNil
  returns zero for arbitrary source term indices.
- The internal proofs use actual registry equations, checked decoder inverse,
  PA induction, and equality transport. Native evaluate/Encodable calibration is
  not reflected into internal proofs.
- No runtime append Program or append-preservation theorem is supplied. No entry
  context/formula projections or actual rule2/rule3 checking Program is installed
  into the existing chosen HistoryMachine kernel. Full HB2/HB3 remain unpaid.
