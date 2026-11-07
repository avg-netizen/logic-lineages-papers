source /workspace/scratch/95d226e72a26/toolchain/native-env.sh
export LEAN_CHECK_LOCK_DIR=/workspace/scratch/95d226e72a26/toolchain/locks
cd /workspace/scratch/95d226e72a26/logic-lineages-papers/formalization
python3 scripts/check.py --memory-mib 2048 --rss-mib 1536 --min-free-mib 2048 --threads 1 --cpu-seconds 90 --timeout 180 \
  LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCollectionTargets \
  LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaCodingTargets \
  LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalResidueBoundTargets
