# A model check of the append's claim (encoding/P2.md §2, OBLIGATIONS.md M17), as `Core.withClaim` emits it for lane 0
# of each warp: step 1 reads the owner word (single-copy atomic, A41); step 2, if the word holds this launch's epoch,
# holds iff it equals `mine`; step 3 otherwise holds iff `atom.cas(word, cur, mine)` returns `cur`.
#
# In one launch, the warps that claim one word are for one head and distinct sequences (one warp per (sequence, head),
# and the word is the page's and the head's). The check runs every interleaving of the steps of three such warps, from
# every start value of the word (epochs 0 to 3, sequences 0 to 3), at epochs 1 to 3, and requires that at most one
# claim holds. It also shows why the launch contract makes launches that share the owners run one at a time: two
# overlapping launches at epochs 1 and 2 can both hold a claim of one word.
#
# Run by check.sh; it takes a fraction of a second.
import itertools, sys


def claims(order, warps, word):
    """The claims that hold when `warps` ((epoch, sequence) each) run their steps in `order`, from `word`."""
    cur, held = {}, {}
    for w in order:
        epoch, seq = warps[w]
        mine = (epoch << 32) | seq
        if w not in cur:  # step 1
            cur[w] = word
            if cur[w] >> 32 == epoch:  # step 2
                held[w] = cur[w] == mine
        elif w not in held:  # step 3
            prev = word
            if word == cur[w]:
                word = mine
            held[w] = prev == cur[w]
    return [held[w] for w in range(len(warps))]


def orders(n):
    """Every interleaving of `n` warps' two steps each (a warp that stops after step 2 ignores its second)."""
    return set(itertools.permutations([w for w in range(n) for _ in range(2)]))


def doubled(warps):
    """The (start word, order) pairs under which two claims hold."""
    return [(word, order) for e0 in range(4) for s0 in range(4) for word in [(e0 << 32) | s0]
            for order in orders(len(warps)) if sum(claims(order, warps, word)) > 1]


failed = False
for epoch in (1, 2, 3):
    bad = doubled([(epoch, 0), (epoch, 1), (epoch, 2)])
    print(f"{'ok  ' if not bad else 'FAIL'} one launch at epoch {epoch}, three sequences: {len(bad)} schedules hold twice")
    failed |= bool(bad)
bad = doubled([(1, 0), (2, 1)])
print(f"{'ok  ' if bad else 'FAIL'} two overlapping launches at epochs 1 and 2: {len(bad)} schedules hold twice, as M17 says")
failed |= not bad
sys.exit(1 if failed else 0)
