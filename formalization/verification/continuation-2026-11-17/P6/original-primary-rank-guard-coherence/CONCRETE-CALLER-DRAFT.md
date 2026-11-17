# Actual caller draft

Export: Proof.rankGuardCoherence : Targets.InternalRankGuardCoherence.
Generic helpers GuardProof and MinimumMemberProof are parent-owned/native verified.
Concrete caller by installed_edge: Definitions abbreviates unchanged original T,Q,E,L,P,R.
RootRanksProof uses actual minimum membership and primary-rank preservation to
derive actual sameRank acceptance. RootMinimumRank/SeedRank/Pair query witnesses.
AtMinimumsProof derives both admissions from the original request, applies root
adapter twice, compares each guarded output to its true minimum via GuardProof,
and uses exact original MinimumCoherence. CandidatePair/TargetMinimum/SeedMinimum
queries eliminate all auxiliary observations before the frozen endpoint.
No source/window activation assumption, rank equality oracle, fallback oracle,
extra public minimum or candidate pair observation is introduced.

All concrete proofs are pending native checks and require genuine pending raw
rank and primary-rank suppliers. Frozen target/comparator unchanged.
