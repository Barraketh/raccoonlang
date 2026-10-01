# Tensor-memory splits the core must refuse: checks/emitted.rac with one change each. Run by check.sh through
# gpu/mutate.py. (The mutants of the attention example, gpu/ATTENTION.md §5, are still to come.)

SOURCE = "encoding/checks/emitted.rac"

MUTANTS = [
    dict(
        name="split_at_32", expect="EvidenceNotDischarged", mentions="multiple of 64",
        why="Splits the lower half 32 columns in: a multiple of the allocation unit, but not of the 64 columns that "
            "A27 assumes for MMA and tcgen05.ld/st addresses and H3 tests, so generation records an error and "
            "`render` refuses the kernel.",
        old="""  def inner : Nat := 128""",
        new="""  def inner : Nat := 32""",
    ),
]
