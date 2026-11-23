# Original open packed erase state: nil and matching head
The local eraser transcribes the actual historical right-fold scratch
state, retaining the surviving list and a found flag. The checked
nil and matching-head proofs are on the literal AST: a matching head
with no previously removed tail occurrence yields the same tail and a
found flag of one. The other branches and existence from membership
for arbitrary open codes are not asserted.
