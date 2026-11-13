# Next literal transition kernel design (not frozen specs)

1. Native codec totality for Nat/product/Option/list, yielding every Nat code
is the encoding of an actual HistoryMachine.State. List totality follows by
strong induction on the code, with tail code bounded by right_le_pair. This
would discharge original decodedState/default behavior on all vectors. It is
native calibration only and must never be reflected into internal arithmetic.

2. Explicit kernel with arguments [state,index,fuel]. Decode the state pair
into Option History and List Line. For nil remaining lines return state.
For a cons line pop its tail; NONE stays NONE; SOME history runs the fixed
literal dispatcher. Gate acceptance with actual equalCode(check,1), not
arbitrary nonzero. On acceptance cons the decoded (context,raw) entry and
return its SOME code paired with remaining lines; otherwise return NONE.

3. Prove actual internal equalCode correctness (one iff equal) from existing
actual difference laws and doubleZero. This is necessary because native leaf
calibration cannot imply internal Boolean range.

4. Prove successful-step extension at arbitrary runtime terms: an actual
kernel step from pair(SOME h,cons line rest) to pair(SOME out,rest) implies
the corresponding step after appending tail to h yields SOME append(out,tail).
Only successful old-step is a logical premise. Prove actual structural step
laws and derive dispatcher acceptance through exact equality guard equations.

5. Build a NEW same-source tuple from this literal kernel, retaining calibrated
bound/initial/finalizer and all fuel/fusion laws. Prove its actual installed
kernel and append addresses and add the universally closed step-extension
clause. Do not assert identity with, mutate, or silently replace the old opaque
kernel tuple. Iterator extension, certificate shape/index construction and
HB3 producer invariants remain further obligations.
